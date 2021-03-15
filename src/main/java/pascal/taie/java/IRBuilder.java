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

package pascal.taie.java;

import pascal.taie.ir.IR;
import pascal.taie.java.classes.JMethod;
import pascal.taie.oldpta.ir.PTAIR;

public interface IRBuilder {

    /**
     * Build IR for concrete methods.
     */
    IR buildIR(JMethod method);

    PTAIR buildPTAIR(JMethod method);

    /**
     * Build IR for all methods in the given hierarchy.
     */
    void buildAll(ClassHierarchy hierarchy);

    void buildAllPTA(ClassHierarchy hierarchy);
}
