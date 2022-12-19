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
import org.neo4j.driver.*;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.heap.TaintObj;
import pascal.taie.analysis.pta.core.solver.*;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.IRPrinter;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Pair;
import pascal.taie.util.collection.ThreePair;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.neo4j.driver.Values.parameters;
import static pascal.taie.analysis.pta.core.solver.PointerFlowEdge.Kind.*;

public class TaintAnalysis implements Plugin {

    private static final Logger logger = LogManager.getLogger(TaintAnalysis.class);

    /**
     * Map from method (which is source method) to set of types of
     * taint objects returned by the method calls.
     */
    private final MultiMap<JMethod, Type> sources = Maps.newMultiMap();

    /**
     * Map from method (which causes taint transfer) to set of relevant
     * {@link TaintTransfer}.
     */
    private final MultiMap<JMethod, TaintTransfer> transfers = Maps.newMultiMap();

    /**
     * Map from variable to taint transfer information.
     * The taint objects pointed to by the "key" variable are supposed
     * to be transferred to "value" variable with specified type.
     */
    private MultiMap<Var, ThreePair<Var, Type, String>> varTransfers = Maps.newMultiMap();
    private MultiMap<JMethod, Var> sinkInfo = Maps.newMultiMap();

    private Solver solver;

    private CSManager csManager;

    private Context emptyContext;

    private TaintManager manager;

    private TaintConfig config;
    private boolean entryTaint = true;
    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        manager = new TaintManager(solver.getHeapModel());
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                solver.getHierarchy(),
                solver.getTypeSystem());
        logger.info(config);
        config.getSources().forEach(s ->
                sources.put(s.method(), s.type()));
        config.getTransfers().forEach(t -> {
            transfers.put(t.method(), t);
        });
    }

    public void onNewCSMethod(CSMethod csEntry) {
        if (!entryTaint)
            return;
        entryTaint = false;
        JMethod entry = csEntry.getMethod();
        Context ctx = csEntry.getContext();
        List<Var> params = entry.getIR().getParams();
        for (int i = 0; i < 1; i++) {
            Var param = params.get(i);
            Type type = param.getType();
            Pointer pointer = csManager.getCSVar(ctx, param);
            Obj taint = manager.makeTaint(null, type, entry.getSignature()+ " begin");
            solver.addVarPointsTo(csEntry.getContext(), param, emptyContext, taint);
        }
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        Invoke callSite = edge.getCallSite().getCallSite();
        JMethod caller = callSite.getMethodRef().resolve();
        String methodRef = callSite.getMethodRef().toString();
        JMethod callee = edge.getCallee().getMethod();
        // generate taint value from source call
//        Var lhs = callSite.getLValue();
//        if (lhs != null && sources.containsKey(callee)) {
//            sources.get(callee).forEach(type -> {
//                Obj taint = manager.makeTaint(callSite, type);
//                solver.addVarPointsTo(edge.getCallSite().getContext(), lhs,
//                        emptyContext, taint);
//            });
//        }
        // process sinks
        config.getSinks().forEach(sink -> {
            if (caller == sink.method()) {
                Var var = getVar(callSite, sink.index());
//                String methodFormat = String.format("%s:%s", callSite.getInvokeExp().)
                sinkInfo.put(sink.method(), var);
            }
        });
        // process taint transfer
        transfers.get(caller).forEach(transfer -> {
            Var from = getVar(callSite, transfer.from());
            Var to = getVar(callSite, transfer.to());
            String stmt = callSite.format();
            // when transfer to result variable, and the call site
            // does not have result variable, then "to" is null.
            if (to != null) {
                Type type = transfer.type();
                // propagate when csFrom contains taintObj
                // another resolve: varTransfers.put(from, new ThreePair<>(to, type, stmt));
                Context ctx = edge.getCallSite().getContext();
                CSVar csFrom = csManager.getCSVar(ctx, from);
                PointsToSet pts = solver.getPointsToSetOf(csFrom);
                CSObj taint = pts.getTaint();
                TaintTrans taintTrans = new TaintTrans(type, solver);
                if (taint != null) {
                    solver.addVarPointsTo(ctx, to, emptyContext, manager.makeTaint(taint.getObject(), type, stmt));
                    taintTrans.setPropagate(false);
                }
                solver.addPFGEdge(csFrom, csManager.getCSVar(ctx, to), PointerFlowEdge.Kind.TAINT, taintTrans);
            }
        });
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
//        CSObj taint = pts.getTaint();
//        if (taint == null)
//            return;
//        Var var = csVar.getVar();
//        Context ctx = csVar.getContext();
//        MultiMap<Var, ThreePair<Var, Type, String>> varTrans = Maps.newMultiMap();
//        varTransfers.get(var).forEach(pair ->
//                solver.addVarPointsTo(ctx, pair.first(), emptyContext, manager.makeTaint(taint.getObject(), pair.second(), pair.thrid())));
//        // only transfer one time for var
//        varTransfers.removeAll(var);
    }

    /**
     * Retrieves variable from a call site and index.
     */
    private static Var getVar(Invoke callSite, int index) {
        InvokeExp invokeExp = callSite.getInvokeExp();
        return switch (index) {
            case TaintTransfer.BASE -> ((InvokeInstanceExp) invokeExp).getBase();
            case TaintTransfer.RESULT -> callSite.getResult();
            default -> invokeExp.getArg(index);
        };
    }

    @Override
    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        PointerAnalysisResult result = solver.getResult();
        Set<TaintFlow> taintFlows = new TreeSet<>();
        sinkInfo.forEach((methodRef, var) -> {
//            result.getPointsToSet(var).forEach(obj -> {
//                if (obj instanceof TaintObj) {
//                    System.out.println("----------------------------");
//                    System.out.println(obj.toString());
//                    System.out.println("----------------------------");
//                }
//            });
            System.out.printf("Find sink: %s with %s in %s\n", methodRef, var.toString(), var.getMethod());
        });
        long num = result.getObjects().stream().filter(manager::isTaint).count();
        System.out.printf("total %d taintObj\n", num);
//        printTaint(result);
        showRelation();
        return taintFlows;
    }

    private void showRelation() {
        var graph = new NeoGraph("bolt://localhost:7687", "neo4j", "password");
        solver.getPFG().getPointers().forEach(p -> {
            p.getOutEdges().forEach(e -> {
                if (e.getTransfer().hasTaint()) {
                    System.out.println(e.format());
                    graph.addRelation(e);
                }
            });
        });
        sinkInfo.forEach((sink, var) -> {
            graph.addRelation(var, sink);
        });
    }
    private void printTaint(PointerAnalysisResult result) {
        Map<JMethod, List> taints = new HashMap();
        result.getVars().forEach(var -> {
            if (var.getMethod().toString().startsWith("<ognl.") && //!p.matcher(var.getName()).matches() &&
                    result.getPointsToSet(var).stream().filter(manager::isTaint).count() > 0){
                        JMethod method = var.getMethod();
                String name = var.getName();
                if (taints.containsKey(method)) {
                    taints.get(method).add(name);
                } else {
                    List<String> names = new ArrayList<>();
                    names.add(name);
                    taints.put(method, names);
                }
            }
        });
        taints.forEach((method, names) -> {
            System.out.println("----------------------------");
            System.out.println(method.toString());
            method.getIR().forEach(s -> System.out.println(IRPrinter.toString(s)));
            System.out.println(names.toString());
            System.out.println("----------------------------");
        });
    }
}
class NeoGraph implements AutoCloseable {
    private final Driver driver;
    private Session session;

    public NeoGraph(String uri, String user, String password) {
        driver = GraphDatabase.driver(uri, AuthTokens.basic(user, password));
        session = driver.session();
    }

    @Override
    public void close() throws RuntimeException {
        driver.close();
    }

    private String handle1(String info) {
        String[] des = info.split(":");
        if (des.length == 2) {
            var query = new Query("MERGE (r:Class {name:$class}) MERGE(s:Field {name:$field}) MERGE (r)-[:hasField]->(s)",
                    parameters("class", des[0], "field", des[1]));
            session.run(query);
            return String.format("Field {name:\"%s\"}", des[1]);
        } else {
            var query = new Query("MERGE (r:Class {name:$class}) MERGE(s:Method {name:$method}) MERGE (r)-[:hasMethod]->(s)",
                    parameters("class", des[0], "method", des[1]));
            session.run(query);
            var query1 = new Query("MERGE (r:Method {name:$method}) MERGE(s:Var {name:$var}) MERGE (r)-[:hasVar]->(s)",
                    parameters("method", des[1], "var", des[2]));
            session.run(query1);
            return String.format("Var {name:\"%s\"}", des[2]);
        }
    }

    private String handle(String info) {
        String[] des = info.split(":");
        if (des.length == 2) {
            return String.format("Field {name:\"%s\", class:\"%s\"}", des[1], des[0]);
        } else {
            return String.format("Method {name:\"%s\", class:\"%s\"}", des[1], des[0]);
        }
    }
    private String handle(Var var) {
        return String.format("Method {name:\"%s\", class:\"%s\"}", var.getMethod().getName(), var.getMethod().getDeclaringClass());
    }

    private String handle(JMethod method) {
        return String.format("Method {name:\"%s\", class:\"%s\"}", method.getName(), method.getDeclaringClass());
    }
    private String handle(JField field) {
        return String.format("Field {name:\"%s\", class:\"%s\"}", field.getDeclaringClass(), field.getName());
    }

//    public void addRelation(String info) {
//        String[] edge = info.split("-");
//        String[] src = edge[0].split(":");
//        String[] target = edge[2].split(":");
//        var query = new Query(String.format("MERGE (r:%s) MERGE (s:%s) MERGE (r)-[:%s]->(s)", handle(edge[0]), handle(edge[2]), edge[1]));
//        session.run(query);
//    }
    public void addRelation(PointerFlowEdge edge) {
        PointerFlowEdge.Kind kind = edge.getKind();
        if (EnumSet.of(PARAMETER_PASSING, RETURN, CALL, TAINT).contains(kind)){
            String src = edge.getSource().format();
            String target = edge.getTarget().format();
            var query = new Query(String.format("MERGE (r:%s) MERGE (s:%s) MERGE (r)-[:%s]->(s)", handle(src), handle(target), kind));
            session.run(query);
        }
    }

    public void addRelation(Var var, JMethod sink) {
        var query = new Query(String.format("MERGE (r:%s) MERGE (s:%s) MERGE (r)-[:SINK]->(s)", handle(var), handle(sink)));
        session.run(query);
    }
    public void addRelation(String name1, String name2) {
        var query = new Query("MERGE (r:Person {name:$name1}) MERGE (s:Person {name:$name2}) MERGE (r)-[:FRIEND_OF]->(s)",
                parameters("name1", name1, "name2", name2));
        session.run(query);
    }
}
