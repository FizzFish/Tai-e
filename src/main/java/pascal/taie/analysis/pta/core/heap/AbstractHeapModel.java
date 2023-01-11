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

package pascal.taie.analysis.pta.core.heap;

import pascal.taie.World;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.ReferenceLiteral;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.TwoKeyMap;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static pascal.taie.language.classes.ClassNames.STRING;
import static pascal.taie.language.classes.ClassNames.STRING_BUFFER;
import static pascal.taie.language.classes.ClassNames.STRING_BUILDER;
import static pascal.taie.language.classes.ClassNames.THROWABLE;

/**
 * All heap models should inherit this class, and we can define
 * some uniform behaviors of heap modeling here.
 */
public abstract class AbstractHeapModel implements HeapModel {

    private final boolean isMergeStringConstants;

    private final boolean isMergeStringObjects;

    private final boolean isMergeStringBuilders;

    private final boolean isMergeExceptionObjects;

    private final TypeSystem typeSystem;

    private final ClassType string;

    private final ClassType stringBuilder;

    private final ClassType stringBuffer;

    private final ClassType throwable;

    private final Map<New, NewObj> newObjs = Maps.newMap();

    private final TwoKeyMap<Type, ReferenceLiteral, ConstantObj> constantObjs
            = Maps.newTwoKeyMap();

    /**
     * The merged object representing string constants.
     */
    private final MergedObj mergedSC;

    private final Map<Type, MergedObj> mergedObjs = Maps.newMap();

    private final Map<MockObj, MockObj> mockObjs = Maps.newMap();

    /**
     * Counter for indexing Objs.
     */
    private int counter = 0;

    private final List<Obj> objs = new ArrayList<>(1024);

    protected AbstractHeapModel(AnalysisOptions options) {
        isMergeStringConstants = options.getBoolean("merge-string-constants");
        isMergeStringObjects = options.getBoolean("merge-string-objects");
        isMergeStringBuilders = options.getBoolean("merge-string-builders");
        isMergeExceptionObjects = options.getBoolean("merge-exception-objects");
        typeSystem = World.get().getTypeSystem();
        string = typeSystem.getClassType(STRING);
        stringBuilder = typeSystem.getClassType(STRING_BUILDER);
        stringBuffer = typeSystem.getClassType(STRING_BUFFER);
        throwable = typeSystem.getClassType(THROWABLE);
        mergedSC = add(new MergedObj(string, "<Merged string constants>"));
    }

    @Override
    public Obj getObj(New allocSite) {
        Type type = allocSite.getRValue().getType();
        if (isMergeStringObjects && type.equals(string)) {
            return getMergedObj(allocSite);
        }
        if (isMergeStringBuilders &&
                (type.equals(stringBuilder) || type.equals(stringBuffer))) {
            return getMergedObj(allocSite);
        }
        if (isMergeExceptionObjects && typeSystem.isSubtype(throwable, type)) {
            return getMergedObj(allocSite);
        }
        return doGetObj(allocSite);
    }

    /**
     * Merges given object given by its type.
     *
     * @param allocSite the allocation site of the object
     * @return the merged object
     */
    protected MergedObj getMergedObj(New allocSite) {
        MergedObj mergedObj = mergedObjs.computeIfAbsent(
                allocSite.getRValue().getType(),
                t -> add(new MergedObj(t, "<Merged " + t + ">")));
        mergedObj.addRepresentedObj(getNewObj(allocSite));
        return mergedObj;
    }

    protected NewObj getNewObj(New allocSite) {
        return newObjs.computeIfAbsent(allocSite,
                site -> add(new NewObj(site)));
    }

    /**
     * The method which controls the heap modeling for normal objects.
     */
    protected abstract Obj doGetObj(New allocSite);

    @Override
    public Obj getConstantObj(ReferenceLiteral value) {
        Obj obj = doGetConstantObj(value);
        if (isMergeStringConstants && value.getType().equals(string)) {
            mergedSC.addRepresentedObj(obj);
            return mergedSC;
        }
        return obj;
    }

    protected Obj doGetConstantObj(ReferenceLiteral value) {
        return constantObjs.computeIfAbsent(value.getType(), value,
                (t, v) -> add(new ConstantObj(v)));
    }

    @Override
    public Obj getMockObj(String desc, Object alloc, Type type, JMethod container) {
        MockObj mockObj = new MockObj(desc, alloc, type, container);
        return mockObjs.computeIfAbsent(mockObj, this::add);
    }

    public TaintObj getTaintObj(JMethod method, Type type) {
        TaintObj taintObj = new TaintObj(method, type);
        add(taintObj);
        return taintObj;
    }
    public TaintObj getTaintObj(Obj parent, Type type, Stmt allocation) {
        TaintObj taintObj = new TaintObj(parent, type, allocation);
        add(taintObj);
        return taintObj;
    }
    public GenObj getGenObj(Stmt stmt, Type type) {
        GenObj genObj = new GenObj(stmt, type);
        add(genObj);
        return genObj;
    }

    /**
     * Adds an obj to this model. This method also sets index for given obj.
     * Each obj should be passed to this method only once.
     */
    protected <T extends Obj> T add(T obj) {
        objs.add(obj);
        obj.setIndex(counter++);
        return obj;
    }

    @Override
    public Collection<Obj> getObjects() {
        return Collections.unmodifiableList(objs);
    }

    @Override
    public int getIndex(Obj o) {
        return o.getIndex();
    }

    @Override
    public Obj getObject(int index) {
        return objs.get(index);
    }
}
