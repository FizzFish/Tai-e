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

import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.language.classes.JMethod;

/**
 * Representation of load array statement, e.g., x = a[..].
 */
public class LoadArray extends ArrayStmt<Var, ArrayAccess> {

    public LoadArray(Var lvalue, ArrayAccess rvalue) {
        super(lvalue, rvalue);
        rvalue.getBase().addLoadArray(this);
    }

    @Override
    public ArrayAccess getArrayAccess() {
        return getRValue();
    }

    @Override
    public <T> T accept(StmtVisitor<T> visitor) {
        return visitor.visit(this);
    }
    public JMethod getContainer() {
        return getLValue().getMethod();
    }
    public String format() {
        JMethod method = getLValue().getMethod();
        String stmt = String.format("[%s|%s|%s]",
                method.getDeclaringClass(), method.getName(), this);
        return stmt;
    }
}
