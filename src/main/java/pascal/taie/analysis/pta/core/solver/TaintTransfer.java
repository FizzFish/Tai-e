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
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.heap.TaintObj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.language.type.Type;

import java.util.function.Supplier;

public class TaintTransfer implements Transfer {

    private final Supplier<PointsToSet> ptsFactory;
    private final Type type;
    public TaintTransfer(Type type, Solver solver) {
        this.type = type;
        this.ptsFactory = solver::makePointsToSet;
    }
    public boolean hasTaint() {
        return true;
    }
    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        PointsToSet result = ptsFactory.get();
        for (CSObj csobj : input) {
            if (csobj.getObject() instanceof TaintObj)
                result.addObject(csobj);
        }
        return input;
    }
}
