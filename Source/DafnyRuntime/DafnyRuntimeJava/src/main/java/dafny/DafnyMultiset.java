package dafny;

import java.math.BigInteger;
import java.util.*;

public class DafnyMultiset<T> {
    /*
    Invariant: forall x. m.get(x) == null || m.get(x) > 0
    As in Java, null is allowed as a key
    */
    private Map<T, BigInteger> innerMap;

    public DafnyMultiset() {
        innerMap = new HashMap<>();
    }

    // Requires that all values in m are non-negative
    public DafnyMultiset(Map<T, BigInteger> m) {
        assert m != null : "Precondition Violation";
        innerMap = new HashMap<>();
        for (Map.Entry<T, BigInteger> e : m.entrySet()) {
            BigInteger n = e.getValue();
            int cmp = n.compareTo(BigInteger.ZERO);
            assert 0 <= cmp : "Precondition Violation";
            if (0 < cmp) {
                innerMap.put(e.getKey(), n);
            }
        }
    }

    public DafnyMultiset(Set<T> s) {
        assert s != null : "Precondition Violation";
        innerMap = new HashMap<>();
        for (T t : s) {
            incrementMultiplicity(t, BigInteger.ONE);
        }
    }

    public DafnyMultiset(Collection<T> c) {
        assert c != null : "Precondition Violation";
        innerMap = new HashMap<>();
        for (T t : c) {
            incrementMultiplicity(t, BigInteger.ONE);
        }
    }

    // Adds all elements found in the list to a new DafnyMultiSet. The number of occurrences in the list becomes the
    // multiplicity in the DafnyMultiset
    public DafnyMultiset(List<T> l) {
        assert l != null : "Precondition Violation";
        innerMap = new HashMap<>();
        for (T t : l) {
            incrementMultiplicity(t, BigInteger.ONE);
        }
    }

    @SafeVarargs
    public static <T> DafnyMultiset<T> of(T ... args) {
        return new DafnyMultiset<T>(Arrays.asList(args));
    }

    private static final DafnyMultiset<Object> EMPTY = DafnyMultiset.of();

    @SuppressWarnings("unchecked")
    public static <T> DafnyMultiset<T> empty() {
        // Safe because immutable
        return (DafnyMultiset<T>) EMPTY;
    }

    @SuppressWarnings("unchecked")
    public static <T> Type<DafnyMultiset<? extends T>> _type(Type<T> elementType) {
        // Fudge the type parameter; it's not great, but it's safe because
        // (for now) type descriptors are only used for default values
        return Type.referenceWithDefault(
                (Class<DafnyMultiset<? extends T>>) (Class<?>) DafnyMultiset.class,
                DafnyMultiset.empty());
    }

    public BigInteger cardinality() {
        BigInteger sum = BigInteger.ZERO;
        for (BigInteger m : innerMap.values()) {
            sum = sum.add(m);
        }
        return sum;
    }

    // cardinalityInt should be called only if the cardinality is known to fit in an "int"
    public int cardinalityInt() {
        int sum = 0;
        for (BigInteger m : innerMap.values()) {
            sum += m.intValue();
        }
        return sum;
    }

    // Determines if the current object is a subset of the DafnyMultiSet passed in. Requires that the input
    // DafnyMultiset is not null.
    public boolean isSubsetOf(DafnyMultiset other) {
        assert other != null : "Precondition Violation";
        for (Map.Entry<T, BigInteger> entry : innerMap.entrySet()) {
            if (multiplicity(other, entry.getKey()).compareTo(entry.getValue()) < 0) return false;
        }
        return true;
    }

    // Determines if the current object is a proper subset of the DafnyMultiSet passed in. Requires that the input
    // Dafny MultiSet is not null.
    public boolean isProperSubsetOf(DafnyMultiset other) {
        assert other != null : "Precondition Violation";
        return isSubsetOf(other) && this.cardinality().compareTo(other.cardinality()) < 0;
    }

    public boolean contains(Object t) {
        // Relies on invariant that all keys have a positive multiplicity
        return innerMap.containsKey(t);
    }

    public <U> boolean disjoint(DafnyMultiset<? extends U> other) {
        assert other != null : "Precondition Violation";
        for (U u : other.innerMap.keySet()) {
            if (innerMap.containsKey(u)) return false;
        }
        return true;
    }

    public static <T> BigInteger multiplicity(DafnyMultiset<? extends T> th, T t) {
        BigInteger m = th.innerMap.get(t);
        return m == null ? BigInteger.ZERO : m;
    }

    public static <T> DafnyMultiset<T> update(DafnyMultiset<? extends T> th, T t, BigInteger b) {
        assert th != null : "Precondition Violation";
        assert b != null && b.compareTo(BigInteger.ZERO) >= 0 : "Precondition Violation";
        DafnyMultiset<T> copy = new DafnyMultiset<>(((DafnyMultiset<T>)th).innerMap);
        copy.setMultiplicity(t, b);
        return copy;
    }

    // destructively sets multiplicity of t to b; a negative value is treated as 0
    private void setMultiplicity(T t, BigInteger b) {
        assert b != null : "Precondition Violation";
        if (b.compareTo(BigInteger.ZERO) > 0) {
            innerMap.put(t, b);
        } else {
            innerMap.remove(t);
        }
    }

    // destructively adds n (possibly negative) to value of t
    private void incrementMultiplicity(T t, BigInteger b) {
        assert b != null : "Precondition Violation";
        setMultiplicity(t, multiplicity(this, t).add(b));
    }

    public static <T> DafnyMultiset<T> union(DafnyMultiset<? extends T> th, DafnyMultiset<? extends T> other) {
        assert th != null : "Precondition Violation";
        assert other != null : "Precondition Violation";

        DafnyMultiset<T> u = new DafnyMultiset<>(((DafnyMultiset<T>)th).innerMap);
        for (Map.Entry<T, BigInteger> entry : ((DafnyMultiset<T>)other).innerMap.entrySet()) {
            u.incrementMultiplicity(entry.getKey(), entry.getValue());
        }
        return u;
    }

    // Returns a DafnyMultiSet with multiplicities that are
    // max(this.multiplicity(e)-other.multiplicity(e), BigInteger.ZERO)
    public static <T> DafnyMultiset<T> difference(DafnyMultiset<? extends T> th, DafnyMultiset<? extends T> other) {
        assert th != null : "Precondition Violation";
        assert other != null : "Precondition Violation";

        DafnyMultiset<T> u = new DafnyMultiset<>(((DafnyMultiset<T>)th).innerMap);
        for (Map.Entry<T, BigInteger> entry : ((DafnyMultiset<T>)other).innerMap.entrySet()) {
            T key = entry.getKey();
            BigInteger m0 = multiplicity(u, key);
            BigInteger m1 = entry.getValue();
            u.setMultiplicity(key, m0.subtract(m1));
        }
        return u;
    }

    // Returns a DafnyMultiSet with multiplicities that are min(this.multiplicity(e), other.multiplicity(e))
    public static <T> DafnyMultiset<T> intersection(DafnyMultiset<? extends T> th, DafnyMultiset<? extends T> other) {
        assert th != null : "Precondition Violation";
        assert other != null : "Precondition Violation";

        DafnyMultiset<T> u = new DafnyMultiset<>();
        for (Map.Entry<T, BigInteger> entry : ((DafnyMultiset<T>)th).innerMap.entrySet()) {
            T key = entry.getKey();
            BigInteger m0 = entry.getValue();
            BigInteger m1 = multiplicity((DafnyMultiset<T>)other, key);
            u.setMultiplicity(key, m0.min(m1));
        }
        return u;
    }

    public Iterable<T> Elements(){
        ArrayList<T> r = new ArrayList<>();
        for(Map.Entry<T, BigInteger> e : innerMap.entrySet()){
            for(int i = 0; i < e.getValue().intValue(); i++){
                r.add(e.getKey());
            }
        }
        return r;
    }

    public Iterable<T> UniqueElements(){
        return innerMap.keySet();
    }

    @Override
    protected Object clone() throws CloneNotSupportedException {
        return super.clone();
    }

    @Override
    @SuppressWarnings("UNCHECKED_CAST")
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnyMultiset o = (DafnyMultiset) obj;
        return innerMap.equals(o.innerMap);
    }

    @Override
    public int hashCode() {
        return innerMap.hashCode();
    }

    @Override
    public String toString() {
        String s = "multiset{";
        String sep = "";
        for (Map.Entry<T, BigInteger> entry : innerMap.entrySet()) {
            String t = Helpers.toString(entry.getKey());
            BigInteger n = entry.getValue();
            for (BigInteger i = BigInteger.ZERO; i.compareTo(n) < 0; i = i.add(BigInteger.ONE)) {
                s += sep + t;
                sep = ", ";
            }
        }
        return s + "}";
    }
}
