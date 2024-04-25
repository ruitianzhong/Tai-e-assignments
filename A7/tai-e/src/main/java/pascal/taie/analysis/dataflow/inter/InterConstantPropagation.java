/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;

import java.util.LinkedList;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;

    private LinkedList<StoreArray> storeArrays;

    private LinkedList<StoreField> storeFields;

    private LinkedList<LoadArray> loadArrays;

    private LinkedList<LoadField> loadFields;


    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        storeArrays = new LinkedList<>();
        storeFields = new LinkedList<>();
        loadArrays = new LinkedList<>();
        loadFields = new LinkedList<>();
        for (var stmt : icfg) {
            if (stmt instanceof StoreArray storeArray) {
                storeArrays.add(storeArray);
            } else if (stmt instanceof StoreField storeField) {
                storeFields.add(storeField);
            } else if (stmt instanceof LoadField loadField) {
                loadFields.add(loadField);
            } else if (stmt instanceof LoadArray loadArray) {
                loadArrays.add(loadArray);
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt.getDef().isEmpty()) {
            return cp.transferNode(stmt, in, out);
        }

        var lValue = stmt.getDef().get();

        if (!(lValue instanceof Var)) {
            return cp.transferNode(stmt, in, out);
        }
        var copy = out.copy();

        cp.transferNode(stmt, in, copy);

        copy.update((Var) lValue, Value.getUndef());

        return out.copyFrom(copy);

    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof LoadField loadField) {
            return transferLoadField(loadField, in, out);
        } else if (stmt instanceof StoreField storeField) {
            return transferStoreField(storeField, in, out);
        } else if (stmt instanceof StoreArray storeArray) {
            return transferStoreArray(storeArray, in, out);
        } else if (stmt instanceof LoadArray loadArray) {
            return transferLoadArray(loadArray, in, out);
        }
        var out_copy = out.copy();
        var change = cp.transferNode(stmt, in, out);
        if (change) {
            var delta = new CPFact();
            for (var o : out.keySet()) {
                if (!out_copy.keySet().contains(o)) {
                    delta.update(o, out.get(o));
                }
            }
            for (var o : delta.keySet()) {
                for (var loadArray : loadArrays) {
                    var index = loadArray.getArrayAccess().getIndex();
                    System.out.println("index " + index + " o " + o);
                    if (index == o) {
                        solver.addWorkList(loadArray);
                    }
                }
            }
        }
        return change;
    }

    boolean transferLoadField(LoadField loadField, CPFact in, CPFact out) {
        var lvar = loadField.getLValue();
        if (!ConstantPropagation.canHoldInt(lvar)) {
            return out.copyFrom(in);
        }
        // must be int?

        var fieldAccess = loadField.getFieldAccess();
        var in_copy = in.copy();
        var isStatic = fieldAccess.getFieldRef().isStatic();
        for (var storeField : storeFields) {
            if (checkNeedMeet(storeField, loadField, isStatic)) {
                var storeVar = storeField.getRValue();
                var fact = this.solver.getResult().getInFact(storeField);
                Value storeValue = fact.get(storeVar);
                var temp = new CPFact();
                temp.update(lvar, storeValue);
                meetInto(temp, in_copy);
            }
        }

        return out.copyFrom(in_copy);
    }

    private boolean checkNeedMeet(StoreField storeField, LoadField loadField, boolean isStatic) {
        JField sf = storeField.getFieldRef().resolve(),
                lf = loadField.getFieldRef().resolve();
        if (sf != lf) {
            return false;
        }
        if (isStatic) {
            return true;
        }

        var store_var = storeField.getFieldAccess().getUses().get(0);
        var load_var = loadField.getFieldAccess().getUses().get(0);

        if (!(store_var instanceof Var var1 && load_var instanceof Var var2)) {
            throw new AnalysisException("unexpected behavior");
        }

        return checkInstanceFieldAlias(var1, var2);
    }


    private boolean checkInstanceFieldAlias(Var v1, Var v2) {
        var pts2 = pta.getPointsToSet(v2);
        for (var obj1 : pta.getPointsToSet(v1)) {
            if (pts2.contains(obj1)) {
                return true;
            }
        }
        return false;
    }

    boolean transferStoreField(StoreField storeField, CPFact in, CPFact out) {
        var change = out.copyFrom(in);
        if (change) {
            for (var loadField : loadFields) {
                solver.addWorkList(loadField);
            }
        }
        return change;
    }

    boolean transferStoreArray(StoreArray storeArray, CPFact in, CPFact out) {
        var change = out.copyFrom(in);
        if (change) {
            for (var loadArray : loadArrays) {
                solver.addWorkList(loadArray);
            }
        }
        return change;
    }

    boolean transferLoadArray(LoadArray loadArray, CPFact in, CPFact out) {
        var lvar = loadArray.getLValue();
        if (!ConstantPropagation.canHoldInt(lvar)) {
            return out.copyFrom(in); // error here for Reference.java
        }
        var in_copy = in.copy();
        for (var storeArray : storeArrays) {
            var storeBase = storeArray.getArrayAccess().getBase();
            var loadBase = loadArray.getArrayAccess().getBase();
            var loadIndex = loadArray.getArrayAccess().getIndex();
            var storeIndex = storeArray.getArrayAccess().getIndex();
            var fact = solver.getResult().getInFact(storeArray);
            if (checkArrayAlias(storeBase, fact.get(storeIndex), loadBase, in.get(loadIndex))) {
                var storeVar = storeArray.getRValue();
                var temp = new CPFact();
                temp.update(lvar, fact.get(storeVar));
                meetInto(temp, in_copy);
            }
        }
        return out.copyFrom(in_copy);
    }


    private boolean checkArrayAlias(Var storeBase, Value storeIndex, Var loadBase, Value loadIndex) {

        var pts = pta.getPointsToSet(storeBase);
        var found = false;
        for (var p : pta.getPointsToSet(loadBase)) {
            if (pts.contains(p)) {
                found = true;
                break;
            }
        }
        if (!found) {
            return false;
        }
        if (storeIndex.isUndef() || loadIndex.isUndef()) {
            return false;
        }

        if (storeIndex.isNAC() || loadIndex.isNAC()) {
            return true;
        }

        return storeIndex.getConstant() == loadIndex.getConstant();
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        var source = edge.getSource();
        var copy = out.copy();
        if (source instanceof Invoke invokeExp && invokeExp.getDef().isPresent()) {
            System.out.println(source);
            copy.update((Var) invokeExp.getDef().get(), Value.getUndef());
        }
        return copy;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        var temp = new CPFact();
        var j = 0;
        if (edge.getSource() instanceof Invoke invoke) {
            for (var param : edge.getCallee().getIR().getParams()) {
                // all args are `Var` ?
                temp.update(param, callSiteOut.get(invoke.getInvokeExp().getArg(j)));
                j++;
            }
        }
        return temp;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        var target = new CPFact();

        var def = edge.getCallSite().getDef();
        if (def.isEmpty()) {
            return target;
        }

        var lvalue = def.get();

        if (!(lvalue instanceof Var var)) {
            return target;
        }

        for (var retVar : edge.getReturnVars()) {
            var temp = new CPFact();
            temp.update(var, returnOut.get(retVar));
            meetInto(temp, target);
        }
        return target;
    }
}
