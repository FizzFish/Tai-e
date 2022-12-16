package pascal.taie.analysis.pta.core.heap;

import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import java.util.Optional;

public class TaintObj extends Obj{
    private Stmt alloc;
    private final Type type;
    private String des;
    private JMethod container;

    public TaintObj(Stmt alloc, Type type, String des) {
        this.type = type;
        this.alloc = alloc;
        this.des = des;
        this.container = null;
    }

    public Type getType() {
        return type;
    }

    public Object getAllocation() {
        return alloc;
    }

    @Override
    public Optional<JMethod> getContainerMethod() {
        return Optional.ofNullable(container);
    }

    @Override
    public Type getContainerType() {
        return type;
    }

    public String toString() {
        String out = String.format("%s: %s, %s\n", des, type.toString(), alloc);
        return out;
    }
}

