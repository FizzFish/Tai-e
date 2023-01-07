package pascal.taie.analysis.pta.core.heap;

import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import java.util.Optional;

public class TaintObj extends Obj{
    private Obj parent;
    private final Type type;
    private String stmt;
    private JMethod container;
    private int kind = 0;

    public TaintObj(Obj parent, Type type, String stmt) {
        this.type = type;
        this.parent = parent;
        this.stmt = stmt;
        this.container = null;
    }

    public Type getType() {
        return type;
    }

    public Object getAllocation() {
        return stmt;
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
    public boolean isTaint() {
        return kind == 1;
    }

    public void setKind(int kind) {
        this.kind = kind;
    }

    public String toString() {
        TaintObj cur = this;
        String out = "";
        do {
            out += String.format("%s: %s\n", cur.type.toString(), cur.stmt);
            cur = (TaintObj) cur.parent;
        } while (cur != null);
        return out;
    }
}

