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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        var callGraph = solver.getCallGraph();

        for (var csMethod : callGraph) {
            for (var sink : config.getSinks()) {
                if (sink.method() == csMethod.getMethod()) {
                    transferSink(callGraph.getCallersOf(csMethod), taintFlows, sink.index());
                }
            }
        }
        return taintFlows;
    }

    private void transferSink(Set<CSCallSite> callers, Set<TaintFlow> taintFlows, int index) {

        for (var caller : callers) {
            var invokeExp = caller.getCallSite().getInvokeExp();
            for (int i = 0; i < invokeExp.getArgCount(); i++) {
                var arg = invokeExp.getArg(i);
                var pArg = csManager.getCSVar(caller.getContext(), arg);

                for (CSObj obj : pArg.getPointsToSet()) {
                    if (manager.isTaint(obj.getObject()) && i == index) {
                        var taintFlow = new TaintFlow(manager.getSourceCall(obj.getObject()), caller.getCallSite(), i);
                        taintFlows.add(taintFlow);
                    }
                }
            }
        }
    }


    public void transferCallSite(@Nonnull CSCallSite csCallSite, @Nonnull JMethod method, @Nullable CSVar csBase) {
        transferSource(csCallSite, method);
        taintTransfer(csCallSite, method, csBase);
    }

    private void transferSource(CSCallSite csCallSite, JMethod method) {
        Var ret = csCallSite.getCallSite().getLValue();
        if (ret == null) {
            return;
        }
        for (var source : config.getSources()) {
            if (source.method() == method) {
                Obj taintObj = manager.makeTaint(csCallSite.getCallSite(), source.type());
                var pRet = csManager.getCSVar(csCallSite.getContext(), ret);
                var csObj = csManager.getCSObj(emptyContext, taintObj);
                solver.addWorkList(pRet, PointsToSetFactory.make(csObj));
                return;
            }
        }
    }

    private void taintTransfer(CSCallSite csCallSite, JMethod method, CSVar csBase) {

        for (var transfer : config.getTransfers()) {
            if (transfer.method() != method) {
                continue;
            }
            int from = transfer.from(), to = transfer.to();
            var result = csCallSite.getCallSite().getResult();
            CSVar csResult = null;

            if (result != null) {
                csResult = csManager.getCSVar(csCallSite.getContext(), result);
            }

            if (from == -1 && to == -2) {
                // from base to result
                base2result(csBase, csResult);
            }
            if (from >= 0 && to == -1) {
                // from arg to base
                arg2base(csCallSite, csBase, from);
            }
            if (from >= 0 && to == -2) {
                // from arg to result
                arg2result(csCallSite, csResult, from);
            }
        }
    }

    private void base2result(CSVar baseVar, CSVar result) {
        if (result != null && baseVar != null) {
            solver.addPFGEdge(baseVar, result);
        }
    }

    private void arg2result(CSCallSite csCallSite, CSVar csResult, int arg) {
        if (csResult != null) {
            var csArg = csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getInvokeExp().getArg(arg));
            solver.addPFGEdge(csArg, csResult);
        }
    }

    private void arg2base(CSCallSite csCallSite, CSVar baseVar, int arg) {
        if (baseVar != null) {
            var csArg = csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getInvokeExp().getArg(arg));
            solver.addPFGEdge(csArg, baseVar);
        }
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }
}
