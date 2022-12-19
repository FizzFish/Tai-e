package pascal.taie.analysis.pta.core.solver;

import pascal.taie.analysis.pta.pts.PointsToSet;

public class CallTransfer implements Transfer {

    private boolean hasTaintObj;

    public CallTransfer(boolean taint) {
        hasTaintObj = taint;
    }

    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        return null;
    }
    public boolean hasTaint() {
        return hasTaintObj;
    }

    @Override
    public boolean needPropagate() {
        return false;
    }
}
