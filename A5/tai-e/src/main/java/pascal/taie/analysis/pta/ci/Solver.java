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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.contains(method)) {
            return;
        }
        callGraph.addReachableMethod(method);
        for (var stmt : method.getIR().getStmts()) {
            System.out.println(stmt);
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(Copy copy) {
            Var lv = copy.getLValue(), rv = copy.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(rv), pointerFlowGraph.getVarPtr(lv));
            return null;
        }

        @Override
        public Void visit(New stmt) {
            if (stmt.getDef().isEmpty()) {
                return null;
            }
            LValue lvalue = stmt.getDef().get();

            Pointer p;
            if (lvalue instanceof Var var) {
                p = pointerFlowGraph.getVarPtr(var);
            } else {
                throw new AnalysisException("unexpected right value");
            }

            var obj = heapModel.getObj(stmt);
            PointsToSet pointsToSet = new PointsToSet(obj);
            workList.addEntry(p, pointsToSet);
            return null;
        }

        @Override
        public Void visit(LoadField loadField) {
            if (loadField.getDef().isEmpty() || !loadField.getFieldRef().isStatic()) {
                logger.log(Level.ALL, "non-static field");
                return null;
            }

            var def = loadField.getDef().get();
            var field = loadField.getFieldRef().resolve();
            if (def instanceof Var var) {
                addPFGEdge(pointerFlowGraph.getStaticField(field), pointerFlowGraph.getVarPtr(var));
            }
            return null;
        }

        @Override
        public Void visit(StoreField storeField) {
            if (!storeField.isStatic()) {
                return null;
            }

            var field = storeField.getFieldRef().resolve();
            var var = storeField.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(var), pointerFlowGraph.getStaticField(field));
            return null;
        }

        @Override
        public Void visit(Invoke invoke) {
            if (invoke.isStatic()) {
                JMethod method = resolveCallee(null, invoke);
                addReachable(method);
                linkArgAndRet(invoke, method);
                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method));
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target) && !source.getPointsToSet().isEmpty()) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {

            var entry = workList.pollEntry();
            var p = entry.pointer();
            var delta = propagate(p, entry.pointsToSet());

            if (p instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();

                for (var obj : delta) {
                    for (LoadField e : var.getLoadFields()) {
                        var instanceField = pointerFlowGraph.getInstanceField(obj, e.getFieldRef().resolve());
                        addPFGEdge(instanceField, pointerFlowGraph.getVarPtr(e.getLValue()));
                    }

                    for (StoreField e : var.getStoreFields()) {
                        var instanceField = pointerFlowGraph.getInstanceField(obj, e.getFieldRef().resolve());
                        addPFGEdge(pointerFlowGraph.getVarPtr(e.getRValue()), instanceField);
                    }

                    for (StoreArray e : var.getStoreArrays()) {
                        var array = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(pointerFlowGraph.getVarPtr(e.getRValue()), array);
                    }

                    for (LoadArray e : var.getLoadArrays()) {
                        var array = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(array, pointerFlowGraph.getVarPtr(e.getLValue()));
                    }

                    processCall(var, obj);
                }
            }


        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var set = pointer.getPointsToSet();
        var delta = new PointsToSet();
        for (var obj : pointsToSet) {
            if (set.contains(obj)) {
                continue;
            }
            delta.addObject(obj);
            set.addObject(obj);
        }

        if (!delta.isEmpty()) {
            for (var p : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(p, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (var invoke : var.getInvokes()) {
            var method = resolveCallee(recv, invoke);
            addReachable(method);
            processNonStaticCall(invoke, method, recv);
            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method));
        }
    }

    private void processNonStaticCall(Invoke invoke, JMethod method, Obj recv) {
        var thisVar = method.getIR().getThis();
        workList.addEntry(pointerFlowGraph.getVarPtr(thisVar), new PointsToSet(recv));
        linkArgAndRet(invoke, method);
    }

    private void linkArgAndRet(Invoke invoke, JMethod method) {

        int i = 0;
        for (var param : method.getIR().getParams()) {
            var arg = invoke.getInvokeExp().getArg(i);
            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
            i++;
        }

        var lvalue = invoke.getLValue();
        if (lvalue != null) {
            for (var ret : method.getIR().getReturnVars()) {
                addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(lvalue));
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
