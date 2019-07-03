package DafnyClasses;

public class DafnyTuple2<T0, T1> {
    private T0 _0;
    private T1 _1;

    public DafnyTuple2(T0 _0, T1 _1) {
        this._0 = _0;
        this._1 = _1;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnyTuple2<T0, T1> o = (DafnyTuple2<T0, T1>) obj;
        return this._0.equals(o._0) && this._1.equals(o._1);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(_0.toString());
        sb.append(", ");
        sb.append(_1.toString());
        sb.append(")");
        return sb.toString();
    }

    @Override
    public int hashCode() {
        // GetHashCode method (Uses the djb2 algorithm)
        // https://stackoverflow.com/questions/1579721/why-are-5381-and-33-so-important-in-the-djb2-algorithm
        long hash = 5381;
        hash = ((hash << 5) + hash) + 0;
        hash = ((hash << 5) + hash) + ((long) this._0.hashCode());
        hash = ((hash << 5) + hash) + ((long) this._1.hashCode());
        return (int) hash;
    }

    public T0 get_0() { return this._0; }

    public T1 get_1() { return this._1; }
}

