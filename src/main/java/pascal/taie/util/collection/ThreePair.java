package pascal.taie.util.collection;

public record ThreePair<T1, T2, T3>(T1 first, T2 second, T3 thrid) {

    @Override
    public String toString() {
        return "<" + first + ", " + second + ", " + thrid + ">";
    }
}
