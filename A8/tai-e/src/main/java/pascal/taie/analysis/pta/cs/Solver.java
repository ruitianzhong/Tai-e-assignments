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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import javax.annotation.Nonnull;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.contains(csMethod)) {
            return;
        }
        callGraph.addReachableMethod(csMethod);
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        for (var stmt : csMethod.getMethod().getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    public void addPFGEdge(@Nonnull Pointer source, @Nonnull Pointer target) {
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

            if (p instanceof CSVar csVar) {
                var context = csVar.getContext();
                for (var obj : delta) {
                    var var = csVar.getVar();
                    for (var e : var.getLoadArrays()) {
                        var target = csManager.getCSVar(context, e.getLValue());
                        var source = csManager.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    }
                    for (var e : var.getStoreArrays()) {
                        var source = csManager.getCSVar(context, e.getRValue());
                        var target = csManager.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    }
                    for (var e : var.getLoadFields()) {
                        var source = csManager.getInstanceField(obj, e.getFieldRef().resolve());
                        var target = csManager.getCSVar(context, e.getLValue());
                        addPFGEdge(source, target);
                    }

                    for (var e : var.getStoreFields()) {
                        var source = csManager.getCSVar(context, e.getRValue());
                        var target = csManager.getInstanceField(obj, e.getFieldRef().resolve());
                        addPFGEdge(source, target);
                    }
                    processCall(csVar, obj);
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
        var delta = PointsToSetFactory.make();
        var set = pointer.getPointsToSet();
        for (var p : pointsToSet) {
            if (set.contains(p)) {
                continue;
            }
            delta.addObject(p);
            set.addObject(p);
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (var callSite : recv.getVar().getInvokes()) {
            var method = resolveCallee(recvObj, callSite);
            var csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
            var newContext = contextSelector.selectContext(csCallSite, recvObj, method);

            var csMethod = csManager.getCSMethod(newContext, method);
            addReachable(csMethod);

            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), csCallSite, csMethod));

            var thisVar = method.getIR().getThis();
            var csThisVar = csManager.getCSVar(newContext, thisVar);

            linkParamAndReturn(callSite, method, recv.getContext(), newContext);
            taintAnalysis.transferCallSite(csCallSite, method, recv);
            workList.addEntry(csThisVar, PointsToSetFactory.make(recvObj));
        }
    }

    private void linkParamAndReturn(Invoke stmt, JMethod method, Context oldContext, Context newContext) {
        int i = 0;
        for (var param : method.getIR().getParams()) {
            Pointer pParam = csManager.getCSVar(newContext, param), pArg = csManager.getCSVar(oldContext, stmt.getInvokeExp().getArg(i));
            addPFGEdge(pArg, pParam);
            i++;
        }
        var lvalue = stmt.getLValue();
        if (lvalue != null) {
            for (var ret : method.getIR().getReturnVars()) {
                Pointer pRet = csManager.getCSVar(newContext, ret), pValue = csManager.getCSVar(oldContext, lvalue);
                addPFGEdge(pRet, pValue);
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            if (stmt.getDef().isEmpty()) {
                return null;
            }

            var lvalue = stmt.getDef().get();
            Pointer p;
            if (lvalue instanceof Var var) {
                p = csManager.getCSVar(context, var);
            } else {
                throw new AnalysisException("unexpected type");
            }
            // CSObj Vs. Obj
            Obj obj = heapModel.getObj(stmt);
            Context newContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(newContext, obj);
            workList.addEntry(p, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var rvalue = stmt.getRValue(), lvalue = stmt.getLValue();
            addPFGEdge(csManager.getCSVar(context, rvalue), csManager.getCSVar(context, lvalue));
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            JMethod method = resolveCallee(null, stmt);

            var csCallSite = csManager.getCSCallSite(context, stmt);
            var newContext = contextSelector.selectContext(csCallSite, method);
            var csMethod = csManager.getCSMethod(newContext, method);
            addReachable(csMethod);

            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, csMethod));
            linkParamAndReturn(stmt, method, context, newContext);
            taintAnalysis.transferCallSite(csCallSite, method, null);
            return null;
        }

        @Override
        public Void visit(LoadField loadField) {

            if (!loadField.getFieldRef().isStatic()) {
                return null;
            }
            var lvalue = loadField.getLValue();
            var rvalue = loadField.getRValue();

            var staticField = csManager.getStaticField(rvalue.getFieldRef().resolve());
            var pVar = csManager.getCSVar(context, lvalue);

            addPFGEdge(staticField, pVar);

            return null;
        }

        @Override
        public Void visit(StoreField storeField) {
            if (!storeField.isStatic()) {
                return null;
            }
            var field = csManager.getStaticField(storeField.getFieldRef().resolve());
            var var = csManager.getCSVar(context, storeField.getRValue());
            addPFGEdge(var, field);
            return null;
        }
    }

    public void addWorkList(Pointer p, PointsToSet pointsToSet) {
        if (!pointsToSet.isEmpty()) {
            workList.addEntry(p, pointsToSet);
        }
    }

    public CSCallGraph getCallGraph() {
        return callGraph;
    }
}
