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

import java.util.HashSet;
import java.util.Set;

import static pascal.taie.ir.exp.ArithmeticExp.Op.*;
import static pascal.taie.ir.exp.BitwiseExp.Op.*;
import static pascal.taie.ir.exp.ConditionExp.Op.*;
import static pascal.taie.ir.exp.ShiftExp.Op.*;

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
        CPFact cpfact = new CPFact();
        for(Var param: cfg.getIR().getParams()) {
            if(canHoldInt(param)) {
                cpfact.update(param, Value.getNAC());
            }
        }
        return cpfact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        Set<Var> allVars = new HashSet<>(target.keySet());
        allVars.addAll(fact.keySet());
        for(Var var: allVars) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if(v1.isUndef()) {
            return v2;
        } else if(v2.isUndef()) {
            return v1;
        } else if(v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else {
            return v1 == v2 ? v1 : Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact old_out = out.copy();
        out.copyFrom(in);
        if(stmt instanceof DefinitionStmt<?, ?> dstmt) {
            LValue l = dstmt.getLValue();
            if(l instanceof Var var && canHoldInt(var)) {
                RValue r = dstmt.getRValue();
                out.update(var, evaluate(r, in));
            }
        }
        return !old_out.equals(out);
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
        if(exp instanceof IntLiteral intltr) {
            return Value.makeConstant(intltr.getValue());
        } else if(exp instanceof Var var) {
            return in.get(var);
        } else if(exp instanceof BinaryExp bexp) {
            Value v1 = in.get(bexp.getOperand1());
            Value v2 = in.get(bexp.getOperand2());
            if((bexp.getOperator() == DIV || bexp.getOperator() == REM) &&
                    (v2.isConstant() && v2.getConstant() == 0)) {
                return Value.getUndef();
            }
            if(v1.isConstant() && v2.isConstant()) {
                int i1 = v1.getConstant();
                int i2 = v2.getConstant();
                int res = 0;
                BinaryExp.Op op = bexp.getOperator();
                if(bexp instanceof ArithmeticExp) {
                    if(op == ADD) {
                        res = i1 + i2;
                    } else if(op == SUB) {
                        res = i1 - i2;
                    } else if(op == MUL) {
                        res = i1 * i2;
                    } else if(op == DIV) {
                        if(i2 == 0) return Value.getUndef();
                        res = i1 / i2;
                    } else if(op == REM) {
                        if(i2 == 0) return Value.getUndef();
                        res = i1 % i2;
                    }
                } else if(bexp instanceof ConditionExp) {
                    if(op == EQ) {
                        res = i1 == i2 ? 1 : 0;
                    } else if(op == NE) {
                        res = i1 != i2 ? 1 : 0;
                    } else if(op == LT) {
                        res = i1 < i2 ? 1 : 0;
                    } else if(op == GT) {
                        res = i1 > i2 ? 1 : 0;
                    } else if(op == LE) {
                        res = i1 <= i2 ? 1 : 0;
                    } else if(op == GE) {
                        res = i1 >= i2 ? 1 : 0;
                    }
                } else if(bexp instanceof ShiftExp) {
                    if(op == SHL) {
                        res = i1 << i2;
                    } else if(op == SHR) {
                        res = i1 >> i2;
                    } else if(op == USHR) {
                        res = i1 >>> i2;
                    }
                } else if(bexp instanceof BitwiseExp) {
                    if(op == OR) {
                        res = i1 | i2;
                    } else if(op == AND) {
                        res = i1 & i2;
                    } else if(op == XOR) {
                        res = i1 ^ i2;
                    }
                }
                return Value.makeConstant(res);
            } else if(v1.isNAC() || v2.isNAC()) {

                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        } else {
            return Value.getNAC();
        }
    }
}
