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
import soot.jimple.IfStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // Control-Flow Unreachable
        Map<Stmt, Boolean> isReachable = new HashMap<>();
        for(Stmt stmt: cfg.getNodes()) {
            isReachable.put(stmt, false);
        }
        Stack<Stmt> stmtStack = new Stack<>();
        stmtStack.push(cfg.getEntry());
        isReachable.put(cfg.getEntry(), true);
        while(!stmtStack.isEmpty()) {
            Stmt stmt = stmtStack.pop();
            Value condVal = null;
            Value swVal = null;
            boolean swDefault = false;
            if(stmt instanceof If ifStmt) {
                Value val = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(stmt));
                if(val.isConstant()) {
                    condVal = Value.makeConstant(val.getConstant());
                }
            } else if(stmt instanceof SwitchStmt swStmt) {
                Value val = ConstantPropagation.evaluate(swStmt.getVar(), constants.getInFact(stmt));
                if(val.isConstant()) {
                    swVal = Value.makeConstant(val.getConstant());
                    if(!swStmt.getCaseValues().contains(val.getConstant())) swDefault = true;
                }
            }
            for(Edge<Stmt> edge: cfg.getOutEdgesOf(stmt)) {
                Stmt succ = edge.getTarget();
                if(isReachable.get(succ)) continue;
                if(condVal != null) {
                    if(edge.getKind() == Edge.Kind.IF_TRUE && condVal.getConstant() == 0) continue;
                    if(edge.getKind() == Edge.Kind.IF_FALSE && condVal.getConstant() == 1) continue;
                } else if(swVal != null) {
                    if(edge.getKind() == Edge.Kind.SWITCH_CASE && swVal.getConstant() != edge.getCaseValue()) continue;
                    if(edge.getKind() == Edge.Kind.SWITCH_DEFAULT && !swDefault) continue;
                }
                isReachable.put(succ, true);
                stmtStack.push(succ);
            }
        }
        for(Stmt stmt: isReachable.keySet()) {
            if(cfg.isExit(stmt)) continue;
            if(!isReachable.get(stmt) ||
                    (stmt instanceof AssignStmt<?,?> aStmt &&
                    aStmt.getLValue() instanceof Var var &&
                    !liveVars.getResult(stmt).contains(var)) &&
                    hasNoSideEffect(aStmt.getRValue())) {
                deadCode.add(stmt);
            }
        }

        return deadCode;
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
}
