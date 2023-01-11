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

import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ReferenceType;
import pascal.taie.language.type.Type;

import java.awt.*;
import java.util.Optional;

/**
 * Objects that are created by new statements.
 */
public class GenObj extends Obj {

    protected final Stmt allocSite;
    protected final Type type;
    private final JMethod container;

    GenObj(Stmt allocSite, Type type) {
        this.allocSite = allocSite;
        this.type = type;
        this.container = null;
    }

    @Override
    public Type getType() {
        return type;
    }

    @Override
    public Stmt getAllocation() {
        return allocSite;
    }

    @Override
    public Optional<JMethod> getContainerMethod() {
        return Optional.ofNullable(container);
    }

    @Override
    public Type getContainerType() {
        return type;
    }

    @Override
    public boolean isPolymorphism() {
        return true;
    }

    @Override
    public String toString() {
        return String.format("GenObj[%s]", type);
    }
}
