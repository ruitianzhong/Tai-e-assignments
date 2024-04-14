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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (var variable : fact.keySet()) {
            Value v1 = target.get(variable), v2 = fact.get(variable);
            target.update(variable, meetValue(v1, v2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        // v1 or v2 is NAC
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return Value.makeConstant(v1.getConstant());
            } else {
                return Value.getNAC();
            }
        }
        if (v1.isUndef() && v2.isUndef()) {
            return Value.getUndef();
        }

        if (v1.isConstant()) {
            return Value.makeConstant(v1.getConstant());
        }

        if (v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        }

        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        var in_copy = in.copy();

        var def = stmt.getDef();
        if (def.isPresent() && (def.get() instanceof Var var) && canHoldInt(var)) {
            in_copy.update((Var) def.get(), Value.getUndef());
            var rvalues = stmt.getUses();
            for (var rvalue : rvalues) {
                Value value = evaluate(rvalue, in);
                if (value != null) {
                    in.update(var, value);
                }
            }

        }
        return out.copyFrom(in_copy);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var) {
            return evaluateVar((Var) exp, in);
        } else if (exp instanceof BinaryExp) {
            return evaluateBinaryExp((BinaryExp) exp, in);
        } else if (exp instanceof IntLiteral) {
            return evaluateConstant((IntLiteral) exp);
        }
        return null;
    }

    private static Value evaluateVar(Var var, CPFact cpFact) {
        return cpFact.get(var);
    }

    private static Value evaluateConstant(IntLiteral intLiteral) {
        return Value.makeConstant(intLiteral.getValue());
    }

    private static Value evaluateBinaryExp(BinaryExp binaryExp, CPFact cpFact) {

        Value v1 = cpFact.get(binaryExp.getOperand1()), v2 = cpFact.get(binaryExp.getOperand2());
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() || v2.isUndef()) {
            return Value.getUndef();
        }

        int op1 = v1.getConstant(), op2 = v2.getConstant();
        if (binaryExp instanceof ArithmeticExp) {
            return evaluateArithmetic((ArithmeticExp) binaryExp, op1, op2);
        } else if (binaryExp instanceof BitwiseExp) {
            return evaluateBitwise((BitwiseExp) binaryExp, op1, op2);
        } else if (binaryExp instanceof ConditionExp) {
            return evaluateCondition((ConditionExp) binaryExp, op1, op2);
        } else if (binaryExp instanceof ShiftExp) {
            return evaluateShift((ShiftExp) binaryExp, op1, op2);
        }
        return null;
    }

    private static Value evaluateArithmetic(ArithmeticExp exp, int op1, int op2) {

        return switch (exp.getOperator()) {
            case ADD -> Value.makeConstant(op1 + op2);
            case DIV -> op2 == 0 ? Value.getUndef() : Value.makeConstant(op1 / op2);
            case MUL -> Value.makeConstant(op1 * op2);
            case REM -> op2 == 0 ? Value.getUndef() : Value.makeConstant(op1 % op2);
            case SUB -> Value.makeConstant(op1 - op2);
        };

    }

    private static Value evaluateShift(ShiftExp exp, int op1, int op2) {
        return switch (exp.getOperator()) {
            case SHL -> Value.makeConstant(op1 << op2);
            case SHR -> Value.makeConstant(op1 >> op2);
            case USHR -> Value.makeConstant(op1 >>> op2);
        };
    }

    private static Value evaluateCondition(ConditionExp exp, int op1, int op2) {
        return switch (exp.getOperator()) {
            case EQ -> mapCondition(op1 == op2);
            case GE -> mapCondition(op1 >= op2);
            case GT -> mapCondition(op1 > op2);
            case LE -> mapCondition(op1 <= op2);
            case LT -> mapCondition(op1 < op2);
            case NE -> mapCondition(op1 != op2);
        };
    }

    private static Value mapCondition(boolean condition) {
        return condition ? Value.makeConstant(1) : Value.makeConstant(0);
    }

    private static Value evaluateBitwise(BitwiseExp exp, int op1, int op2) {
        return switch (exp.getOperator()) {
            case OR -> Value.makeConstant(op1 | op2);
            case AND -> Value.makeConstant(op1 & op2);
            case XOR -> Value.makeConstant(op1 ^ op2);
        };
    }
}
