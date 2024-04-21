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
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

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
        // TODO - finish me
        LinkedList<JMethod> list = new LinkedList<>();
        callGraph.addReachableMethod(entry);
        list.add(entry);
        while (!list.isEmpty()) {
            var method = list.pop();

            for (var callSite : callGraph.callSitesIn(method).toList()) {
                for (var m : resolve(callSite)) {
                    if (m == null) {
                        continue;
                    }
                    var edge = new Edge<>(CallGraphs.getCallKind(callSite), callSite, m);
                    callGraph.addEdge(edge);

                    if (!callGraph.contains(m)) {
                        callGraph.addReachableMethod(m);
                        list.add(m);
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
        // TODO - finish me
        var ref = callSite.getMethodRef();
        var jClass = ref.getDeclaringClass();
        var subsignature = ref.getSubsignature();
        Set<JMethod> set = new HashSet<>();
        var kind = CallGraphs.getCallKind(callSite);

        if (kind == CallKind.INTERFACE || kind == CallKind.VIRTUAL) {
            LinkedList<JClass> list = new LinkedList<>();
            list.add(jClass);

            while (!list.isEmpty()) {
                var j = list.pop();
                if (j.isInterface()) {
                    list.addAll(hierarchy.getDirectImplementorsOf(j));
                    list.addAll(hierarchy.getDirectSubinterfacesOf(j));
                } else {
                    list.addAll(hierarchy.getDirectSubclassesOf(j));
                }
                var method = dispatch(j, subsignature);
                if (method != null) {
                    set.add(method);
                }
            }
        } else {
            var method = dispatch(jClass, subsignature);
            if (method != null) {
                set.add(method);
            }
        }
        return set;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass.isInterface()) {
            return null;
        }

        JClass j = jclass;
        while (j != null) {
            var method = j.getDeclaredMethod(subsignature);
            if (method != null && !method.isAbstract()) {
                return method;
            }
            j = j.getSuperClass();
        }

        return null;
    }
}
