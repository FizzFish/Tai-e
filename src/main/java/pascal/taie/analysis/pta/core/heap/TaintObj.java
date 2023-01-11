package pascal.taie.analysis.pta.core.heap;

import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import java.util.Optional;

public class TaintObj extends GenObj{
    private Obj parent;
    private Kind kind;
    private String trace;

    public TaintObj(TaintObj parent, Type type, Stmt allocSite) {
        super(allocSite, type);
        this.parent = parent;
        kind = parent.kind;
        trace = allocSite.format();
    }
    public TaintObj(JMethod method, Type type) {
        super(null, type);
        parent = null;
        kind = Kind.TAINT;
        trace = method.getSignature();
    }

    public boolean isTaint() {
        return kind == Kind.TAINT;
    }

    public void setKind(Kind kind) {
        this.kind = kind;
    }
    public Kind getKind() {return kind;}

    public String toString() {
        TaintObj cur = this;
        String out = "";
        do {
            out += String.format("%s: %s\n", cur.type.toString(), cur.trace);
            cur = (TaintObj) cur.parent;
        } while (cur != null);
        return out;
    }
}

