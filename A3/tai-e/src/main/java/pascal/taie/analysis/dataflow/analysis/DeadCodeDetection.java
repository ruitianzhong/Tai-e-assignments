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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        var list = new LinkedList<Stmt>();
        HashSet<Stmt> visited = new HashSet<>(), reached = new HashSet<>();

        var entry = cfg.getEntry();
        list.add(entry);
        visited.add(entry);
        DeadCodeAnalysisContext context = new DeadCodeAnalysisContext(reached, visited, list, cfg, constants, liveVars);

        while (!list.isEmpty()) {
            var stmt = list.pop();
            if (stmt instanceof If) {
                handleIfStmt(context, stmt);
            } else if (stmt instanceof SwitchStmt) {
                handleSwitchStmt(context, stmt);
            } else if (stmt instanceof AssignStmt<?, ?>) {
                handleAssignStmt(context, stmt);
            } else {
                context.reach.add(stmt);
                addAllSuccessors(context, stmt);
            }
        }

        for (var stmt : cfg) {
            if (!visited.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    private void addAllSuccessors(DeadCodeAnalysisContext context, Stmt stmt) {
        for (var edge : context.cfg.getOutEdgesOf(stmt)) {
            if (context.visited.contains(edge.getTarget())) {
                continue;
            }
            context.list.add(edge.getTarget());
        }
    }


    private void handleIfStmt(DeadCodeAnalysisContext context, Stmt stmt) {
        If ifStatement = (If) stmt;
        ConditionExp exp = ifStatement.getCondition();
        var fact = context.constants.getOutFact(stmt);
        Value v1 = fact.get(exp.getOperand1()), v2 = fact.get(exp.getOperand2());

        context.reach.add(stmt);

        if (v1.isNAC() || v2.isNAC()) {
            addAllSuccessors(context, stmt);
            return;
        }
        // attention here
        if (v1.isUndef() || v2.isUndef()) {
            addAllSuccessors(context, stmt);
            return;
        }

        int left = v1.getConstant(), right = v2.getConstant();

        boolean eval = switch (exp.getOperator()) {
            case NE -> left != right;
            case LT -> left < right;
            case LE -> left <= right;
            case GT -> left > right;
            case GE -> left >= right;
            case EQ -> left == right;
        };
        var outEdge = context.cfg.getOutEdgesOf(stmt);
        Stmt realTarget = null;
        for (var edge : outEdge) {
            var target = edge.getTarget();
            if (context.visited.contains(target)) {
                return;
            }
            if (edge.getKind() == Edge.Kind.IF_TRUE && eval) {
                realTarget = target;
            } else if (edge.getKind() == Edge.Kind.IF_FALSE && !eval) {
                realTarget = target;
            }
        }

        if (realTarget != null) {
            addList(context, realTarget);
        }
    }

    private void addList(DeadCodeAnalysisContext context, Stmt target) {
        context.list.add(target);
        context.visited.add(target);
    }

    private void handleSwitchStmt(DeadCodeAnalysisContext context, Stmt stmt) {
        var switchStmt = (SwitchStmt) stmt;
        context.reach.add(stmt);
        var value = context.constants.getOutFact(stmt).get(switchStmt.getVar());
        if (value.isConstant()) {
            var constant = value.getConstant();
            for (var target : switchStmt.getCaseTargets()) {
                if (target.first() == constant) {
                    if (!context.visited.contains(target.second())) {
                        addList(context, target.second());
                        return;
                    }
                }

            }
            if (!context.visited.contains(switchStmt.getDefaultTarget())) {
                addList(context, switchStmt.getDefaultTarget());
            }
        }
    }

    private void handleAssignStmt(DeadCodeAnalysisContext context, Stmt stmt) {
        var assignStmt = (AssignStmt<?, ?>) stmt;
        var lvalue = assignStmt.getLValue();
        var rvalue = assignStmt.getRValue();

        var fact = context.liveVars.getInFact(stmt);

        if (!hasNoSideEffect(rvalue) || (lvalue instanceof Var var && fact.contains(var))) {
            context.reach.add(stmt);
        }

        addAllSuccessors(context, stmt);

    }

    static class DeadCodeAnalysisContext {
        HashSet<Stmt> reach;
        HashSet<Stmt> visited;
        LinkedList<Stmt> list;

        CFG<Stmt> cfg;

        DataflowResult<Stmt, CPFact> constants;

        DataflowResult<Stmt, SetFact<Var>> liveVars;

        DeadCodeAnalysisContext(HashSet<Stmt> reach, HashSet<Stmt> visited, LinkedList<Stmt> list, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, DataflowResult<Stmt, SetFact<Var>> liveVars) {
            this.reach = reach;
            this.visited = visited;
            this.list = list;
            this.cfg = cfg;
            this.constants = constants;
            this.liveVars = liveVars;
        }

    }
}
