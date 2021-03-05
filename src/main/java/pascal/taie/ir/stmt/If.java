/*
 * Tai-e: A Program Analysis Framework for Java
 *
 * Copyright (C) 2020 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2020 Yue Li <yueli@nju.edu.cn>
 * All rights reserved.
 *
 * This software is designed for the "Static Program Analysis" course at
 * Nanjing University, and it supports a subset of Java features.
 * Tai-e is only for educational and academic purposes, and any form of
 * commercial use is disallowed.
 */

package pascal.taie.ir.stmt;

import pascal.taie.ir.exp.ConditionExp;

/**
 * Representation of if statement, e.g., if a == b goto L;
 */
public class If extends AbstractStmt {

    private final ConditionExp condition;

    private final Stmt target;

    public If(ConditionExp condition, Stmt target) {
        this.condition = condition;
        this.target = target;
    }

    public ConditionExp getCondition() {
        return condition;
    }

    public Stmt getTarget() {
        return target;
    }

    @Override
    public String toString() {
        return String.format("if (%s) goto %d", condition, target.getIndex());
    }
}