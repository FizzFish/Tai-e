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
import pascal.taie.util.collection.ThreePair;

import java.util.*;

import static org.neo4j.driver.Values.parameters;
import static pascal.taie.analysis.pta.core.solver.PointerFlowEdge.Kind.*;

public class TaintAnalysis implements Plugin {

    private static final Logger logger = LogManager.getLogger(TaintAnalysis.class);

    /**
     * Map from method (which is source method) to set of types of
     * taint objects returned by the method calls.
     */
    private final MultiMap<JMethod, Integer> sources = Maps.newMultiMap();

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
        manager = solver.getTaintManager();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                solver.getHierarchy(),
                solver.getTypeSystem());
        logger.info(config);
        config.getSources().forEach(s ->
                sources.put(s.method(), s.index()));
        config.getTransfers().forEach(t -> {
            transfers.put(t.method(), t);
        });
    }

    public void onNewCSMethod(CSMethod csEntry) {
        if (!entryTaint)
            return;
        JMethod entry = csEntry.getMethod();
        Context ctx = csEntry.getContext();

        for (int i : sources.get(entry)) {
            Var thisVar = entry.getIR().getThis();
            Obj genThis = manager.makeGen(null, thisVar.getType());
            solver.addVarPointsTo(csEntry.getContext(), thisVar, emptyContext, genThis);
            List<Var> params = entry.getIR().getParams();
            Var param = params.get(i);
            Type type = param.getType();
            Pointer pointer = csManager.getCSVar(ctx, param);
            Obj taint = manager.makeTaint(null, type, entry.getSignature()+ " begin");
            solver.addVarPointsTo(csEntry.getContext(), param, emptyContext, taint);
            entryTaint = false;
        }
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        Invoke callSite = edge.getCallSite().getCallSite();
        JMethod caller = callSite.getMethodRef().resolve();
        Context ctx = edge.getCallSite().getContext();
        String stmt = callSite.format();
        // generate taint value from source call
        // process sinks
        config.getSinks().forEach(sink -> {
            if (caller == sink.method()) {
                Var var = getVar(callSite, sink.index());
                sinkInfo.put(sink.method(), var);
            }
        });
//        if (caller.getName().equals("<init>")) {
//            for (Var arg : callSite.getInvokeExp().getArgs()) {
//                CSVar csArg = csManager.getCSVar(ctx, arg);
//                PointsToSet pts = solver.getPointsToSetOf(csArg);
//                Var base = getVar(callSite, -1);
//                CSObj taint = pts.getTaint();
//                TaintTrans taintTrans = new TaintTrans(base.getType(), solver);
//                if (taint != null) {
//                    solver.addVarPointsTo(ctx, base, emptyContext, manager.makeTaint(taint.getObject(), base.getType(), stmt));
//                    taintTrans.setPropagate(false);
//                    break;
//                }
//                solver.addPFGEdge(csArg, csManager.getCSVar(ctx, base), PointerFlowEdge.Kind.TAINT, taintTrans);
//            }
//        }
        transfers.get(caller).forEach(transfer -> {
            Var from = getVar(callSite, transfer.from());
            Var to = getVar(callSite, transfer.to());

            // when transfer to result variable, and the call site
            // does not have result variable, then "to" is null.
            if (to != null) {
                if (transfer.kind().equals("trans")) {
                    CSVar csFrom = csManager.getCSVar(ctx, from);
                    solver.addPFGEdge(csFrom, csManager.getCSVar(ctx, to), JDK_TRANS);
                } else {
                    int kind = 1;
                    if (transfer.kind().equals("config"))
                        kind = 0;
                    Type returnType = to.getType();

                    // propagate when csFrom contains taintObj
                    // another resolve: varTransfers.put(from, new ThreePair<>(to, type, stmt));
                    CSVar csFrom = csManager.getCSVar(ctx, from);
                    PointsToSet pts = solver.getPointsToSetOf(csFrom);
                    CSObj taint = pts.getTaint();
                    TaintTrans taintTrans = new TaintTrans(returnType, solver, stmt, kind);
                    if (taint != null) {
                        TaintObj newTaint = manager.makeTaint(taint.getObject(), returnType, stmt);
                        newTaint.setKind(kind);
                        solver.addVarPointsTo(ctx, to, emptyContext, newTaint);
                        taintTrans.setPropagate(false);
                    }
                    solver.addPFGEdge(csFrom, csManager.getCSVar(ctx, to), PointerFlowEdge.Kind.TAINT, taintTrans);
                }
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
        MultiMap<JMethod, Var> sinkResult = Maps.newMultiMap();
        // clear unTaint sinkVar
        sinkInfo.forEach((method, var) -> {
            if (result.getPointsToSet(var).stream().filter(manager::isTaint).count() > 0) {
                sinkResult.put(method, var);
                System.out.printf("Find sink: %s with %s in %s\n", method, var.toString(), var.getMethod());
            }
        });
        sinkInfo = sinkResult;
        printTaint(result);
//        showRelation();
        return taintFlows;
    }

    private void showRelation() {
        var graph = new NeoGraph("bolt://localhost:7687", "neo4j", "password");
        solver.getPFG().getPointers().forEach(p -> {
            p.getOutEdges().forEach(e -> {
                if (e.getTransfer().hasTaint() && e.getSource() != e.getTarget()) {
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
        System.out.println(result.getVars().size());
        result.getVars().forEach(var -> {
            if (result.getPointsToSet(var).stream().filter(manager::isTaint).count() > 0){
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
    public void addRelation(PointerFlowEdge edge) {
        PointerFlowEdge.Kind kind = edge.getKind();
//        if (EnumSet.of(PARAMETER_PASSING, RETURN, CALL, TAINT).contains(kind)){
            String src = handle(edge.getSource().format());
            String target = handle(edge.getTarget().format());
            if (!src.substring(src.indexOf('{')).equals(target.substring(src.indexOf('{')))) {
                var query = new Query(String.format("MERGE (r:%s) MERGE (s:%s) MERGE (r)-[:%s]->(s)", src, target, kind));
                session.run(query);
            }
//        }
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
