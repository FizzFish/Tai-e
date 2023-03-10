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

package pascal.taie.ir.stmt;

import pascal.taie.analysis.pta.core.heap.GenObj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.CollectionUtils;

import javax.annotation.Nullable;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Representation of invocation statement, e.g., r = o.m(...) or o.m(...).
 */
public class Invoke extends DefinitionStmt<Var, InvokeExp>
        implements Comparable<Invoke> {

    /**
     * The variable receiving the result of the invocation. This field
     * is null if no variable receives the invocation result, e.g., o.m(...).
     */
    @Nullable
    private final Var result;

    /**
     * The invocation expression.
     */
    private final InvokeExp invokeExp;

    /**
     * The method containing this statement.
     */
    private final JMethod container;
    private boolean resolved = false;
    private boolean taintResolved = false;
    private boolean isCollectionStore = false;
    private boolean isCollectionLoad = false;
    private boolean isConfigureLoad = false;
    private GenObj.Kind genObjLevel = GenObj.Kind.OTHER;

    public void setResolved() {
        resolved = true;
    }
    public boolean isResolved() {
        return resolved;
    }
    public Invoke(JMethod method, InvokeExp invokeExp, @Nullable Var result) {
        this.invokeExp = invokeExp;
        this.result = result;
        if (invokeExp instanceof InvokeInstanceExp) {
            Var base = ((InvokeInstanceExp) invokeExp).getBase();
            base.addInvoke(this);
            // record to generate object for invoke needed
            invokeExp.getArgs().forEach(arg -> {
                arg.addArgInvoke(this);
            });
        }
        this.container = method;
        if (!(invokeExp instanceof InvokeDynamic)) {
            String methodRef = getMethodRef().toString();
            if (methodRef.equals("<java.util.List: boolean add(java.lang.Object)>") || methodRef.equals("<java.util.Map: java.lang.Object put(java.lang.Object,java.lang.Object)>"))
                isCollectionStore = true;
            else if (methodRef.equals("<java.util.List: java.lang.Object get(int)>"))
                isCollectionLoad = true;
            else if (methodRef.equals("<java.util.Map: java.lang.Object get(java.lang.Object)>")) {
                isCollectionLoad = true;
                isConfigureLoad = true;
            }
        }
    }
    public Set<JMethod> resolve(Type type, GenObj genObj) {
        Set<JMethod> methods = new HashSet();
        if (genObj.getKind().compareTo(genObjLevel) <= 0 || isDynamic())
            return methods;
        genObjLevel = genObj.getKind();
        methods = getMethodRef().getCacheMethods(type, this);
        return methods;
    }
    public boolean isCollectionStore() {return isCollectionStore;}
    public boolean isCollectionLoad() {return isCollectionLoad;}
    public boolean isConfigureLoad() {return isConfigureLoad;}

    public Invoke(JMethod method, InvokeExp invokeExp) {
        this(method, invokeExp, null);
    }

    @Override
    @Nullable
    public Var getLValue() {
        return result;
    }

    @Nullable
    public Var getResult() {
        return result;
    }

    @Override
    public InvokeExp getRValue() {
        return invokeExp;
    }

    /**
     * @return the invocation expression of this invoke.
     * @see InvokeExp
     */
    public InvokeExp getInvokeExp() {
        return invokeExp;
    }

    /**
     * @return the method reference of this invoke.
     * @see MethodRef
     */
    public MethodRef getMethodRef() {
        return invokeExp.getMethodRef();
    }

    public boolean isVirtual() {
        return invokeExp instanceof InvokeVirtual;
    }

    public boolean isInterface() {
        return invokeExp instanceof InvokeInterface;
    }

    public boolean isSpecial() {
        return invokeExp instanceof InvokeSpecial;
    }

    public boolean isStatic() {
        return invokeExp instanceof InvokeStatic;
    }

    public boolean isDynamic() {
        return invokeExp instanceof InvokeDynamic;
    }

    public JMethod getContainer() {
        return container;
    }

    @Override
    public Optional<LValue> getDef() {
        return Optional.ofNullable(result);
    }

    @Override
    public List<RValue> getUses() {
        return CollectionUtils.append(invokeExp.getUses(), invokeExp);
    }

    @Override
    public <T> T accept(StmtVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public int compareTo(Invoke other) {
        // first compare container methods in alphabet order
        int container = this.container.toString()
                .compareTo(other.container.toString());
        // if both invokes are in the same container method,
        // then compare their indexes
        return container != 0 ? container : index - other.index;
    }

    @Override
    public String toString() {
        String ret = result == null ? "" : result + " = ";
        return String.format("%s[%d@L%d] %s%s",
                container, getIndex(), getLineNumber(), ret, invokeExp);
    }
    public String format() {
        String ret = result == null ? "" : result + " = ";
        return String.format("[%s|%s|%s%s]",
                container.getDeclaringClass(), container.getName(), ret, invokeExp);
    }
}
