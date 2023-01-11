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

package pascal.taie.analysis.pta.core.solver;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.*;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.taint.TaintManager;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.AssignLiteral;
import pascal.taie.ir.stmt.Cast;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.*;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.*;

import static pascal.taie.language.classes.Signatures.FINALIZE;
import static pascal.taie.language.classes.Signatures.FINALIZER_REGISTER;
import static pascal.taie.language.type.PrimitiveType.CHAR;

public class DefaultSolver implements Solver {

    private static final Logger logger = LogManager.getLogger(DefaultSolver.class);

    /**
     * Description for array objects created implicitly by multiarray instruction.
     */
    private static final String MULTI_ARRAY_DESC = "MultiArrayObj";

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private final CSManager csManager;

    private final ClassHierarchy hierarchy;

    private final TypeSystem typeSystem;

    private final PointsToSetFactory ptsFactory;

    /**
     * Whether only analyzes application code.
     */
    private final boolean onlyApp;

    private Plugin plugin;

    private WorkList workList;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private Set<JMethod> reachableMethods;
//    private Set<CSCallSite> reachableCallSite;

    /**
     * Set of classes that have been initialized.
     */
    private Set<JClass> initializedClasses;

    /**
     * Set of methods to be intercepted and ignored.
     */
    private Set<JMethod> ignoredMethods;

    private StmtProcessor stmtProcessor;

    private PointerAnalysisResult result;

    private Queue<CSCallSite> unResolvedCallSite = new ArrayDeque<>();
    private TaintManager taintManager;

    public DefaultSolver(AnalysisOptions options, HeapModel heapModel,
                         ContextSelector contextSelector, CSManager csManager) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.csManager = csManager;
        hierarchy = World.get().getClassHierarchy();
        typeSystem = World.get().getTypeSystem();
        ptsFactory = new PointsToSetFactory(csManager.getObjectIndexer());
        onlyApp = options.getBoolean("only-app");
        taintManager = new TaintManager(heapModel);
    }

    public PointerFlowGraph getPFG() {
        return pointerFlowGraph;
    }
    @Override
    public AnalysisOptions getOptions() {
        return options;
    }

    @Override
    public HeapModel getHeapModel() {
        return heapModel;
    }

    @Override
    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    @Override
    public CSManager getCSManager() {
        return csManager;
    }
    public TaintManager getTaintManager() {
        return taintManager;
    }

    @Override
    public ClassHierarchy getHierarchy() {
        return hierarchy;
    }

    @Override
    public TypeSystem getTypeSystem() {
        return typeSystem;
    }

    @Override
    public CSCallGraph getCallGraph() {
        return callGraph;
    }

    @Override
    public PointsToSet getPointsToSetOf(Pointer pointer) {
        PointsToSet pts = pointer.getPointsToSet();
        if (pts == null) {
            pts = ptsFactory.make();
            pointer.setPointsToSet(pts);
        }
        return pts;
    }

    @Override
    public PointsToSet makePointsToSet() {
        return ptsFactory.make();
    }

    @Override
    public void setPlugin(Plugin plugin) {
        this.plugin = plugin;
    }

    // ---------- solver logic starts ----------

    /**
     * Runs pointer analysis algorithm.
     */
    @Override
    public void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        reachableMethods = Sets.newSet();
        initializedClasses = Sets.newSet();
        ignoredMethods = Sets.newSet();
        stmtProcessor = new StmtProcessor();
        plugin.onStart();
    }

    /**
     * Processes work list entries until the work list is empty.
     */
    private  void analyze() {
        do {
            _analyze();
            if (unResolvedCallSite.isEmpty())
                break;
            while (!unResolvedCallSite.isEmpty()) {
                CSCallSite csCallSite = unResolvedCallSite.poll();
                Invoke callSite = csCallSite.getCallSite();
                if (!callSite.isResolved()) {
                    Var base = ((InvokeInstanceExp) callSite.getInvokeExp()).getBase();
                    Context context = csCallSite.getContext();
                    Pointer csVar = csManager.getCSVar(context, base);
                    GenObj genObj = heapModel.getGenObj(callSite, base.getType());
                    addPointsTo(csVar, context, genObj);
                    break;
                }
            }
        } while(true);
        plugin.onFinish();
    }
    private void _analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            if (entry instanceof WorkList.PointerEntry pEntry) {
                Pointer p = pEntry.pointer();
                PointsToSet pts = pEntry.pointsToSet();
                PointsToSet diff = propagate(p, pts);
                if (!diff.isEmpty() && p instanceof CSVar v) {
                    processInstanceStore(v, diff);
                    processInstanceLoad(v, diff);
                    processArrayStore(v, diff);
                    processArrayLoad(v, diff);
                    processCall(v, diff);
                    if (diff.containTaint())
                        processArgCall(v);
                    plugin.onNewPointsToSet(v, diff);
                }
            } else if (entry instanceof WorkList.CallEdgeEntry eEntry) {
                processCallEdge(eEntry.edge());
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        logger.trace("Propagate {} to {}", pointsToSet, pointer);
        PointsToSet diff = getPointsToSetOf(pointer).addAllDiff(pointsToSet);
        if (!diff.isEmpty()) {
            pointerFlowGraph.getOutEdgesOf(pointer).forEach(edge -> {
                if (edge.getTransfer().needPropagate())
                    addPointsTo(edge.getTarget(), edge.getTransfer().apply(edge, diff));
            });
        }
        return diff;
    }

    /**
     * Processes instance stores when points-to set of the base variable changes.
     *
     * @param baseVar the base variable
     * @param pts     set of new discovered objects pointed by the variable.
     */
    private void processInstanceStore(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (StoreField store : var.getStoreFields()) {
            Var fromVar = store.getRValue();
            if (isConcerned(fromVar)) {
                CSVar from = csManager.getCSVar(context, fromVar);
                pts.forEach(baseObj -> {
                    InstanceField instField = csManager.getInstanceField(
                            baseObj, store.getFieldRef().resolve());
                    addPFGEdge(from, instField, PointerFlowEdge.Kind.INSTANCE_STORE);
                });
            }
        }
    }

    /**
     * Processes instance loads when points-to set of the base variable changes.
     *
     * @param baseVar the base variable
     * @param pts     set of new discovered objects pointed by the variable.
     */
    private void processInstanceLoad(CSVar baseVar, PointsToSet pts) {
        Context context = baseVar.getContext();
        Var var = baseVar.getVar();
        for (LoadField load : var.getLoadFields()) {
            Var toVar = load.getLValue();
            JField field = load.getFieldRef().resolve();
            if (isConcerned(toVar)) {
                CSVar to = csManager.getCSVar(context, toVar);
                pts.forEach(baseObj -> {
                    Obj obj = baseObj.getObject();
                    // y = taint.f; y<=taint
                    if (obj instanceof TaintObj taint && isBasicField(field)) {
                        TaintObj newTaint = taintManager.makeTaint(taint, field.getType(), load);
                        addPointsTo(to, csManager.getCSObj(contextSelector.getEmptyContext(), newTaint));
                    }
                    InstanceField instField = csManager.getInstanceField(
                            baseObj, field);
                    addPFGEdge(instField, to, PointerFlowEdge.Kind.INSTANCE_LOAD);
                    // tmp = this.arr|list
                    if (isArrayOrList(toVar)) {
                        addPFGEdge(to, instField, PointerFlowEdge.Kind.INSTANCE_LOAD_ARR);
                    }
                });
            }
        }
    }
    private boolean isBasicField(JField filed) {
        Type type = filed.getType();
        String typeName = type.getName();
        if (PrimitiveType.isPrimitiveType(typeName))
            return true;
        // java.lang.String, java.util.List/Map
        if (typeName.startsWith("java.lang") || typeName.startsWith("java.util"))
            return true;
        return false;
    }
    private boolean isArrayOrList(Var var) {
        Type type = var.getType();
        if (type instanceof ArrayType)
            return true;
        if (type instanceof ClassType classType) {
            if (classType.getName().startsWith("java.util"))
                return true;
        }
        return false;
    }

    /**
     * Processes array stores when points-to set of the array variable changes.
     *
     * @param arrayVar the array variable
     * @param pts      set of new discovered arrays pointed by the variable.
     * arr[i] = y | list.add(e) | map.put(k, v)
     */
    private void processArrayStore(CSVar arrayVar, PointsToSet pts) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (StoreArray store : var.getStoreArrays()) {
            Var rvalue = store.getRValue();
            if (isConcerned(rvalue)) {
                CSVar from = csManager.getCSVar(context, rvalue);
                pts.forEach(array -> {
                    // arr[i] = y  arr need be ArrayType kind
                    if (array.getObject().getType() instanceof ArrayType) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                        // we need type guard for array stores as Java arrays
                        // are covariant
                        addPFGEdge(from, arrayIndex,
                                PointerFlowEdge.Kind.ARRAY_STORE, arrayIndex.getType());
                    }
                });
                TaintTrans taintTrans = new TaintTrans(rvalue.getType(), this, store, GenObj.Kind.TAINT);
                addPFGEdge(from, arrayVar, PointerFlowEdge.Kind.TAINT, taintTrans);
            }
        }
    }

    /**
     * Processes array loads when points-to set of the array variable changes.
     *
     * @param arrayVar the array variable
     * @param pts      set of new discovered arrays pointed by the variable.
     */
    private void processArrayLoad(CSVar arrayVar, PointsToSet pts) {
        Context context = arrayVar.getContext();
        Var var = arrayVar.getVar();
        for (LoadArray load : var.getLoadArrays()) {
            Var lvalue = load.getLValue();
            CSVar to = csManager.getCSVar(context, lvalue);
            if (isConcerned(lvalue)) {
                pts.forEach(array -> {
                    ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                    // y = arr[i]; arr_index => y
                    addPFGEdge(arrayIndex, to, PointerFlowEdge.Kind.ARRAY_LOAD);
                });
                // y = arr[i]; arr => y
                TaintTrans taintTrans = new TaintTrans(lvalue.getType(), this, load, GenObj.Kind.TAINT);
                addPFGEdge(arrayVar, to, PointerFlowEdge.Kind.TAINT, taintTrans);
            }

        }
    }

    // explore unResolveCallSites with CHA if arg is taint
    private void processArgCall(CSVar csArg) {
        // explore CHA since pts contains taint
        Var arg = csArg.getVar();
        Context context = csArg.getContext();

        arg.getArgInvokes().forEach(callSite -> {
            // explore: empty.virtualCall(taintArg, ...) callee with CHA
            if (!callSite.isResolved()) {
                unResolvedCallSite.add(csManager.getCSCallSite(context, callSite));
            }
        });
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv the receiver variable
     * @param pts  set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, PointsToSet pts) {
        Context context = recv.getContext();
        Var var = recv.getVar();
        for (Invoke callSite : var.getInvokes()) {
            if (callSite.isCollectionLoad()) {
                // y = list.get(0) | y = map.get(k)
                Var lvalue = callSite.getResult();
                CSVar to = csManager.getCSVar(context, lvalue);
                pts.forEach(array -> {
                    ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                    addPFGEdge(arrayIndex, to, PointerFlowEdge.Kind.ARRAY_LOAD);
                });
                if (callSite.isConfigureLoad()) {
                    Var from = callSite.getInvokeExp().getArg(0);
                    CSVar csFrom = csManager.getCSVar(context, from);
                    TaintTrans taintTrans = new TaintTrans(to.getType(), this, callSite, GenObj.Kind.CONFIG);
                    addPFGEdge(csFrom, to, PointerFlowEdge.Kind.TAINT, taintTrans);
                }
            } else if (callSite.isCollectionStore()) {
                // list.add(e) | map.put(k, v)
                Var rvalue = callSite.getInvokeExp().getLastArg();
                CSVar from = csManager.getCSVar(context, rvalue);
                pts.forEach(array -> {
                    ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                    addPFGEdge(from, arrayIndex, PointerFlowEdge.Kind.ARRAY_STORE);
                });
            } else {
                pts.forEach(recvObj -> {
                    Obj obj = recvObj.getObject();
                    Type type = obj.getType();
                    Set<JMethod> methods = new HashSet<>();
                    if (obj instanceof GenObj genObj) {
                        MethodRef methodRef = callSite.getMethodRef();
                        if (methodRef.getDeclaringClass().isApplication()) {
                            methods = callSite.resolve(var.getType(), genObj);
                        } else {
                            JMethod callee = methodRef.resolveNullable();
                            if (callee != null) {
                                methods.add(callee);
                            }
                        }
                    } else {
                        methods.add(CallGraphs.resolveCallee(type, callSite));
                    }
                    if (methods.isEmpty())
                        plugin.onUnresolvedCall(recvObj, context, callSite);
                    else
                        callSite.setResolved();
                    methods.forEach(callee -> {
                        if (callee != null) {
                            // select context
                            CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                            Context calleeContext = contextSelector.selectContext(
                                    csCallSite, recvObj, callee);
                            // build call edge
                            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                            addCallEdge(new Edge<>(CallGraphs.getCallKind(callSite),
                                    csCallSite, csCallee));
                            // pass receiver object to *this* variable
                            if (!isIgnored(callee)) {
                                Var thisVar = callee.getIR().getThis();
                                CSVar CSThis = csManager.getCSVar(calleeContext, thisVar);
                                addVarPointsTo(calleeContext, thisVar, recvObj);
                                Transfer callTransfer = new CallTransfer(recvObj.getObject().isTaint());
                                addPFGEdge(recv, CSThis, PointerFlowEdge.Kind.PARAMETER_PASSING, callTransfer);
                            }
                        }
                    });
                });
            }
        }
    }

    private void processCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (callGraph.addEdge(edge)) {
            // process new call edge
            CSMethod csCallee = edge.getCallee();
            addCSMethod(csCallee);
            if (edge.getKind() != CallKind.OTHER
                    && !isIgnored(csCallee.getMethod())) {
                Context callerCtx = edge.getCallSite().getContext();
                Invoke callSite = edge.getCallSite().getCallSite();
                Context calleeCtx = csCallee.getContext();
                JMethod callee = csCallee.getMethod();
                InvokeExp invokeExp = callSite.getInvokeExp();
                // pass arguments to parameters
                for (int i = 0; i < invokeExp.getArgCount(); ++i) {
                    Var arg = invokeExp.getArg(i);
                    if (isConcerned(arg)) {
                        Var param = callee.getIR().getParam(i);
                        CSVar argVar = csManager.getCSVar(callerCtx, arg);
                        CSVar paramVar = csManager.getCSVar(calleeCtx, param);
                        addPFGEdge(argVar, paramVar, PointerFlowEdge.Kind.PARAMETER_PASSING);
                    }
                }
                // pass results to LHS variable
                Var lhs = callSite.getResult();
                if (lhs != null && isConcerned(lhs)) {
                    CSVar csLHS = csManager.getCSVar(callerCtx, lhs);
                    for (Var ret : callee.getIR().getReturnVars()) {
                        if (isConcerned(ret)) {
                            CSVar csRet = csManager.getCSVar(calleeCtx, ret);
                            addPFGEdge(csRet, csLHS, PointerFlowEdge.Kind.RETURN);
                        }
                    }
                }
            }
            plugin.onNewCallEdge(edge);
        }
    }

    private boolean isIgnored(JMethod method) {
        return ignoredMethods.contains(method) ||
                onlyApp && !method.getDeclaringClass().isApplication();
    }

    /**
     * Processes new reachable methods.
     */
    private void processNewMethod(JMethod method) {
        if (reachableMethods.add(method)) {
            plugin.onNewMethod(method);
        }
    }

//    private void processNewCSInvoke(CSCallSite csCallSite) {
//        if (reachableCallSite.contains(csCallSite))
//            reachableCallSite.add(csCallSite);
//        else
//            plugin.onNewCallSite(csCallSite);
//    }

    /**
     * @return true if the type of given expression is concerned in
     * pointer analysis, otherwise false.
     */
    private static boolean isConcerned(Exp exp) {
        Type type = exp.getType();
        if (type == CHAR)
            return true;
        return type instanceof ReferenceType && !(type instanceof NullType);
    }

    private class StmtProcessor {

        /**
         * Information shared by all visitors.
         */
        private final Map<NewMultiArray, Obj[]> newArrays = Maps.newMap();

        private final Map<New, Invoke> registerInvokes = Maps.newMap();

        private final JMethod finalize = Objects.requireNonNull(
                hierarchy.getJREMethod(FINALIZE));

        private final MethodRef finalizeRef = finalize.getRef();

        private final MethodRef registerRef = Objects.requireNonNull(
                hierarchy.getJREMethod(FINALIZER_REGISTER)).getRef();

        /**
         * Processes given Stmts in given CSMethod.
         */
        private void process(CSMethod csMethod, Collection<Stmt> stmts) {
            StmtVisitor<Void> visitor = new Visitor(csMethod);
            stmts.forEach(stmt -> stmt.accept(visitor));
        }

        /**
         * Visitor that contains actual processing logics.
         */
        private class Visitor implements StmtVisitor<Void> {

            private final CSMethod csMethod;

            private final Context context;

            private Visitor(CSMethod csMethod) {
                this.csMethod = csMethod;
                this.context = csMethod.getContext();
            }

            @Override
            public Void visit(New stmt) {
                // obtain context-sensitive heap object
                NewExp rvalue = stmt.getRValue();
                Obj obj = heapModel.getObj(stmt);
                Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
                addVarPointsTo(context, stmt.getLValue(), heapContext, obj);
                if (rvalue instanceof NewMultiArray) {
                    processNewMultiArray(stmt, heapContext, obj);
                }
                if (hasOverriddenFinalize(rvalue)) {
                    processFinalizer(stmt);
                }
                return null;
            }

            private void processNewMultiArray(
                    New allocSite, Context arrayContext, Obj array) {
                NewMultiArray newMultiArray = (NewMultiArray) allocSite.getRValue();
                Obj[] arrays = newArrays.computeIfAbsent(newMultiArray, nma -> {
                    ArrayType type = nma.getType();
                    Obj[] newArrays = new MockObj[nma.getLengthCount() - 1];
                    for (int i = 1; i < nma.getLengthCount(); ++i) {
                        type = (ArrayType) type.elementType();
                        newArrays[i - 1] = heapModel.getMockObj(MULTI_ARRAY_DESC,
                                allocSite, type, allocSite.getContainer());
                    }
                    return newArrays;
                });
                for (Obj newArray : arrays) {
                    Context elemContext = contextSelector
                            .selectHeapContext(csMethod, newArray);
                    CSObj arrayObj = csManager.getCSObj(arrayContext, array);
                    ArrayIndex arrayIndex = csManager.getArrayIndex(arrayObj);
                    addPointsTo(arrayIndex, elemContext, newArray);
                    array = newArray;
                    arrayContext = elemContext;
                }
            }

            private boolean hasOverriddenFinalize(NewExp newExp) {
                return !finalize.equals(
                        hierarchy.dispatch(newExp.getType(), finalizeRef));
            }

            /**
             * Call Finalizer.register() at allocation sites of objects
             * which override Object.finalize() method.
             * NOTE: finalize() has been deprecated since Java 9, and
             * will eventually be removed.
             */
            private void processFinalizer(New stmt) {
                Invoke registerInvoke = registerInvokes.computeIfAbsent(stmt, s -> {
                    InvokeStatic callSite = new InvokeStatic(registerRef,
                            Collections.singletonList(s.getLValue()));
                    Invoke invoke = new Invoke(csMethod.getMethod(), callSite);
                    invoke.setLineNumber(stmt.getLineNumber());
                    return invoke;
                });
                processInvokeStatic(registerInvoke);
            }

            private void processInvokeStatic(Invoke callSite) {
                JMethod callee = CallGraphs.resolveCallee(null, callSite);
                if (callee != null) {
                    CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
                    Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
                    CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
                    addCallEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee));
                }

            }

            @Override
            public Void visit(AssignLiteral stmt) {
                Literal literal = stmt.getRValue();
                if (isConcerned(literal)) {
                    Obj obj = heapModel.getConstantObj((ReferenceLiteral) literal);
                    Context heapContext = contextSelector
                            .selectHeapContext(csMethod, obj);
                    addVarPointsTo(context, stmt.getLValue(), heapContext, obj);
                }
                return null;
            }

            @Override
            public Void visit(Copy stmt) {
                Var rvalue = stmt.getRValue();
                if (isConcerned(rvalue)) {
                    CSVar from = csManager.getCSVar(context, rvalue);
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    addPFGEdge(from, to, PointerFlowEdge.Kind.LOCAL_ASSIGN);
                    if (isArrayOrList(rvalue))
                        addPFGEdge(to, from, PointerFlowEdge.Kind.LOCAL_ASSIGN);
                }
                return null;
            }

            @Override
            public Void visit(Cast stmt) {
                CastExp cast = stmt.getRValue();
                if (isConcerned(cast.getValue())) {
                    CSVar from = csManager.getCSVar(context, cast.getValue());
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    addPFGEdge(from, to, PointerFlowEdge.Kind.CAST, cast.getType());
                }
                return null;
            }

            /**
             * Processes static load.
             * y = x.f or y = T.f
             */
            @Override
            public Void visit(LoadField stmt) {
                if (stmt.isStatic() && isConcerned(stmt.getRValue())) {
                    JField field = stmt.getFieldRef().resolve();
                    StaticField sfield = csManager.getStaticField(field);
                    CSVar to = csManager.getCSVar(context, stmt.getLValue());
                    addPFGEdge(sfield, to, PointerFlowEdge.Kind.STATIC_LOAD);
                }
                return null;
            }

            /**
             * Processes static store.
             * x.f = y or T.f = y
             */
            @Override
            public Void visit(StoreField stmt) {
                if (stmt.isStatic() && isConcerned(stmt.getRValue())) {
                    JField field = stmt.getFieldRef().resolve();
                    StaticField sfield = csManager.getStaticField(field);
                    CSVar from = csManager.getCSVar(context, stmt.getRValue());
                    addPFGEdge(from, sfield, PointerFlowEdge.Kind.STATIC_STORE);
                }
                return null;
            }

            /**
             * Processes static invocation.
             */
            @Override
            public Void visit(Invoke stmt) {
                if (stmt.isStatic()) {
                    processInvokeStatic(stmt);
                }
                return null;
            }
        }
    }

    // ---------- solver logic ends ----------

    @Override
    public void addPointsTo(Pointer pointer, PointsToSet pts) {
        workList.addEntry(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, CSObj csObj) {
        PointsToSet pts = makePointsToSet();
        pts.addObject(csObj);
        addPointsTo(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, Context heapContext, Obj obj) {
        addPointsTo(pointer, csManager.getCSObj(heapContext, obj));
    }

    @Override
    public void addVarPointsTo(Context context, Var var, PointsToSet pts) {
        addPointsTo(csManager.getCSVar(context, var), pts);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, CSObj csObj) {
        addPointsTo(csManager.getCSVar(context, var), csObj);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, Context heapContext, Obj obj) {
        addPointsTo(csManager.getCSVar(context, var), heapContext, obj);
    }

    @Override
    public void addPFGEdge(Pointer source, Pointer target, PointerFlowEdge.Kind kind,
                           Transfer transfer) {
        PointerFlowEdge edge = new PointerFlowEdge(kind, source, target, transfer);
        if (pointerFlowGraph.addEdge(edge) && edge.getTransfer().needPropagate()) {
            PointsToSet targetSet = transfer.apply(edge, getPointsToSetOf(source));
            if (!targetSet.isEmpty()) {
                addPointsTo(target, targetSet);
            }
        }
    }

    @Override
    public void addEntryPoint(EntryPoint entryPoint) {
        Context entryCtx = contextSelector.getEmptyContext();
        JMethod entryMethod = entryPoint.getMethod();
        CSMethod csEntryMethod = csManager.getCSMethod(entryCtx, entryMethod);
        callGraph.addEntryMethod(csEntryMethod);
        addCSMethod(csEntryMethod);
        IR ir = entryMethod.getIR();
        // pass this objects
        if (!entryMethod.isStatic()) {
            for (Obj thisObj : entryPoint.getThisObjs()) {
                addVarPointsTo(entryCtx, ir.getThis(), entryCtx, thisObj);
            }
        }
        // pass parameter objects
        for (int i = 0; i < entryMethod.getParamCount(); ++i) {
            Var param = ir.getParam(i);
            if (isConcerned(param)) {
                for (Obj paramObj : entryPoint.getParamObjs(i)) {
                    addVarPointsTo(entryCtx, param, entryCtx, paramObj);
                }
            }
        }
    }

    @Override
    public void addCallEdge(Edge<CSCallSite, CSMethod> edge) {
        workList.addEntry(edge);
    }

    @Override
    public void addCSMethod(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            // process new reachable context-sensitive method
            JMethod method = csMethod.getMethod();
            if (isIgnored(method)) {
                return;
            }
            processNewMethod(method);
            addStmts(csMethod, method.getIR().getStmts());
            plugin.onNewCSMethod(csMethod);
        }
    }

    @Override
    public void addStmts(CSMethod csMethod, Collection<Stmt> stmts) {
        stmtProcessor.process(csMethod, stmts);
    }

    @Override
    public void initializeClass(JClass cls) {
        if (cls == null || initializedClasses.contains(cls)) {
            return;
        }
        // initialize super class
        JClass superclass = cls.getSuperClass();
        if (superclass != null) {
            initializeClass(superclass);
        }
        // TODO: initialize the superinterfaces which
        //  declare default methods
        JMethod clinit = cls.getClinit();
        if (clinit != null) {
            // addCSMethod() may trigger initialization of more
            // classes. So cls must be added before addCSMethod(),
            // otherwise, infinite recursion may occur.
            initializedClasses.add(cls);
            CSMethod csMethod = csManager.getCSMethod(
                    contextSelector.getEmptyContext(), clinit);
            addCSMethod(csMethod);
        }
    }

    @Override
    public void addIgnoredMethod(JMethod method) {
        ignoredMethods.add(method);
    }

    @Override
    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, heapModel, callGraph);
        }
        return result;
    }
}
