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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
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
        CPFact fact = new CPFact();
        // 函数参数不能忘记考虑
        for (Var var : cfg.getIR().getParams()) {
            if (canHoldInt(var)) fact.update(var, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var key : fact.keySet()) {
            target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // 1. NAC
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();

        // 2. Undef
        if (v1.isUndef()) return v2;
        else if (v2.isUndef()) return v1;

        // 3. Constant
        if (v1.getConstant() == v2.getConstant()) return Value.makeConstant(v1.getConstant());
        else return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt.getDef().isPresent()) {
            if ((stmt.getDef().get() instanceof Var) && canHoldInt((Var)stmt.getDef().get())) {
                CPFact outTmp = in.copy();
                outTmp.update((Var)stmt.getDef().get(), evaluate(((DefinitionStmt<Var, RValue>)stmt).getRValue(), in));

                if (!outTmp.equals(out)) {
                    for (Var key : outTmp.keySet()) {
                        out.update(key, outTmp.get(key));
                    }
                }

                return outTmp != out;
            }
        }
        if (!in.equals(out)) {
            for (Var key : in.keySet()) {
                out.update(key, in.get(key));
            }
            return true;
        }
        return false;
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
        // 计算给定的表达式
        if (exp instanceof Var) return in.get((Var)exp);
        else if (exp instanceof IntLiteral) return Value.makeConstant(((IntLiteral)exp).getValue());
        else if (exp instanceof BinaryExp) {
            Value v1 = in.get(((BinaryExp)exp).getOperand1());
            Value v2 = in.get(((BinaryExp)exp).getOperand2());
            
            // 情况1: Consider div/mod by zero
            if (v1.isNAC() || v2.isNAC()) {
                if (exp instanceof ArithmeticExp) {
                    if (((ArithmeticExp)exp).getOperator() == ArithmeticExp.Op.DIV && v2.isConstant() && v2.getConstant() == 0) {
                        return Value.getUndef();
                    } else if (((ArithmeticExp)exp).getOperator() == ArithmeticExp.Op.REM && v2.isConstant() && v2.getConstant() == 0) {
                        return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }

            if (v1.isUndef() || v2.isUndef()) return Value.getUndef();

            // 情况2: Consider div/mod by zero
            if (v1.isConstant() && v2.isConstant()) {
                if (exp instanceof ArithmeticExp) {
                    if (((ArithmeticExp)exp).getOperator() == ArithmeticExp.Op.DIV && v2.getConstant() == 0) {
                        return Value.getUndef();
                    } else if (((ArithmeticExp)exp).getOperator() == ArithmeticExp.Op.REM && v2.getConstant() == 0) {
                        return Value.getUndef();
                    }

                    switch (((ArithmeticExp)exp).getOperator()) {
                        case ADD:
                            return Value.makeConstant(v1.getConstant() + v2.getConstant());
                        case SUB:
                            return Value.makeConstant(v1.getConstant() - v2.getConstant());
                        case MUL:
                            return Value.makeConstant(v1.getConstant() * v2.getConstant());
                        case DIV:
                            return Value.makeConstant(v1.getConstant() / v2.getConstant());
                        case REM:
                            return Value.makeConstant(v1.getConstant() % v2.getConstant());
                    }
                } else if (exp instanceof ConditionExp) {
                    switch (((ConditionExp)exp).getOperator()) {
                        case EQ:
                            return Value.makeConstant(v1.getConstant() == v2.getConstant() ? 1 : 0);
                        case NE:
                            return Value.makeConstant(v1.getConstant() != v2.getConstant() ? 1 : 0);
                        case LT:
                            return Value.makeConstant(v1.getConstant() < v2.getConstant() ? 1 : 0);
                        case GT:
                            return Value.makeConstant(v1.getConstant() > v2.getConstant() ? 1 : 0);
                        case LE:
                            return Value.makeConstant(v1.getConstant() <= v2.getConstant() ? 1 : 0);
                        case GE:
                            return Value.makeConstant(v1.getConstant() >= v2.getConstant() ? 1 : 0);
                    }
                } else if (exp instanceof ShiftExp) {
                    switch (((ShiftExp)exp).getOperator()) {
                        case SHL:
                            return Value.makeConstant(v1.getConstant() << v2.getConstant());
                        case SHR:
                            return Value.makeConstant(v1.getConstant() >> v2.getConstant());
                        case USHR:
                            return Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                    }
                } else if (exp instanceof BitwiseExp) {
                    switch (((BitwiseExp)exp).getOperator()) {
                        case OR:
                            return Value.makeConstant(v1.getConstant() | v2.getConstant());
                        case AND:
                            return Value.makeConstant(v1.getConstant() & v2.getConstant());
                        case XOR:
                            return Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                    }
                }
            }

            // 情况3
            return Value.getNAC();
        } else {
            return Value.getNAC();
        }
    }
}
