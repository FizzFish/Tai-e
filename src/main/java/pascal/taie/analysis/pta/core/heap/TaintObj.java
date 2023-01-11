package pascal.taie.analysis.pta.core.heap;

import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import java.util.Optional;

public class TaintObj extends GenObj{
    private Obj parent;
    private int kind = 0;
    private String trace;

    public TaintObj(Obj parent, Type type, Stmt allocSite) {
        super(allocSite, type);
        this.parent = parent;
        if (parent.isTaint())
            kind = 1;
        trace = allocSite.format();
    }
    public TaintObj(JMethod method, Type type) {
        super(null, type);
        parent = null;
        kind = 1;
        trace = method.getSignature();
    }

    public boolean isTaint() {
        return kind == 1;
    }

    public void setKind(int kind) {
        this.kind = kind;
    }
    public int getKind() {return kind;}

    public String toString() {
        TaintObj cur = this;
        String out = "";
        do {
            String stmt = cur.allocSite == null ? "begin" : cur.allocSite.format();
            out += String.format("%s: %s\n", cur.type.toString(), stmt);
            cur = (TaintObj) cur.parent;
        } while (cur != null);
        return out;
    }
}

