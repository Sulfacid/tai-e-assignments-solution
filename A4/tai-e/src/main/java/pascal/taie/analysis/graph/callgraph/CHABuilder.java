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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        callGraph.addReachableMethod(entry);
        Stack<JMethod> workList = new Stack<>();
        Set<JMethod> reachable = new HashSet<>();
        workList.add(entry);
        while(!workList.isEmpty()) {
            JMethod method = workList.pop();
            if(!reachable.contains(method)) {
                reachable.add(method);
                for(Invoke callSite: callGraph.getCallSitesIn(method)) {
                    Set<JMethod> targets = resolve(callSite);
                    for(JMethod target: targets) {
                        if(callGraph.addReachableMethod(target)) {
                            workList.push(target);
                        }
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, target));
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> result = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        JClass dClass = methodRef.getDeclaringClass();
        Subsignature subsign = methodRef.getSubsignature();
        if(callSite.isStatic()) {
            result.add(dClass.getDeclaredMethod(subsign));
        } else if(callSite.isSpecial()) {
            result.add(dispatch(dClass, subsign));
        } else if(callSite.isVirtual() || callSite.isInterface()) {
//            result.add(dispatch(dClass, subsign));
            Stack<JClass> workList = new Stack<>();
            Set<JClass> visited = new HashSet<>();
            workList.add(dClass);
            while(!workList.isEmpty()) {
                JClass cur = workList.pop();
                if(!visited.contains(cur)) {
                    visited.add(cur);
                    JMethod m = dispatch(cur, subsign);
                    if(m != null) result.add(m);
                    workList.addAll(hierarchy.getDirectSubclassesOf(cur));
                    workList.addAll(hierarchy.getDirectSubinterfacesOf(cur));
                    workList.addAll(hierarchy.getDirectImplementorsOf(cur));
                }
            }

        }
//        result.remove(null);
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if(method != null && !method.isAbstract()) {
            return method;
        } else {
            if(jclass.getSuperClass() == null) return null;
            return dispatch(jclass.getSuperClass(), subsignature);
        }
    }
}
