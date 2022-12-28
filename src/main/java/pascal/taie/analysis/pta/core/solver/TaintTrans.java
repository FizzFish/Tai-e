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

import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.TaintObj;
import pascal.taie.analysis.pta.plugin.taint.TaintManager;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.language.type.Type;

import java.util.function.Supplier;

public class TaintTrans implements Transfer {
    private final Type type;
    private final TaintManager manager;
    private final String stmt;
    private final Solver solver;
    private final int kind;
    private boolean needPropagate;
    public TaintTrans(Type type, Solver solver, TaintManager manager, String stmt, int kind) {
        this.type = type;
        this.solver = solver;
        this.needPropagate = true;
        this.manager = manager;
        this.stmt = stmt;
        this.kind = kind;
    }

    public boolean hasTaint() {
        return !needPropagate;
    }
    @Override
    public boolean needPropagate() {
        return needPropagate;
    }
    public void setPropagate(boolean need) {
        needPropagate = need;
    }

    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        PointsToSet result = solver.makePointsToSet();

        CSObj taint = input.getTaint();
        if (taint != null) {
            TaintObj newTaint = manager.makeTaint(taint.getObject(), type, stmt);
            newTaint.setKind(kind);
            CSObj newObj = solver.getCSManager().getCSObj(taint.getContext(), newTaint);
            result.addObject(newObj);
            needPropagate = false;
        }
        return result;
    }
}
