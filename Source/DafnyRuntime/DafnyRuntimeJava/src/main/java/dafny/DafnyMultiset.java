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
            put(e.getKey(), e.getValue());
        }
    }

    public DafnyMultiset(Set<T> s) {
        assert s != null : "Precondition Violation";
        innerMap = new HashMap<>();
        for (T t : s) {
            increment(t, BigInteger.ONE);
        }
    }

    public DafnyMultiset(Collection<T> c) {
        assert c != null : "Precondition Violation";
        innerMap = new HashMap<>();
        for (T t : c) {
            increment(t, BigInteger.ONE);
        }
    }

    // Adds all elements found in the list to a new DafnyMultiSet. The number of occurrences in the list becomes the
    // multiplicity in the DafnyMultiSet
    public DafnyMultiset(List<T> l) {
        assert l != null : "Precondition Violation";
        innerMap = new HashMap<>();
        for (T t : l) {
            increment(t, BigInteger.ONE);
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

    public BigInteger cardinality() {
        BigInteger b = BigInteger.ZERO;
        for (BigInteger big : innerMap.values()) {
            b = b.add(big);
        }
        return b;
    }

    // Determines if the current object is a subset of the DafnyMultiSet passed in. Requires that the input
    // Dafny MultiSet is not null.
    public boolean isSubsetOf(DafnyMultiset<T> other) {
        assert other != null : "Precondition Violation";
        for (Map.Entry<T, BigInteger> entry : innerMap.entrySet()) {
            if (other.multiplicity(entry.getKey()).compareTo(entry.getValue()) < 0) return false;
        }
        return true;
    }

    // Determines if the current object is a proper subset of the DafnyMultiSet passed in. Requires that the input
    // Dafny MultiSet is not null.
    public boolean isProperSubsetOf(DafnyMultiset<T> other) {
        assert other != null : "Precondition Violation";
        return isSubsetOf(other) && this.cardinality().compareTo(other.cardinality()) < 0;
    }

    public boolean contains(T t) {
        // Relies on invariant that all keys have a positive multiplicity
        return innerMap.containsKey(t);
    }

    public boolean disjoint(DafnyMultiset<T> other) {
        assert other != null : "Precondition Violation";
        for (T t : other.innerMap.keySet()) {
            if (innerMap.containsKey(t)) return false;
        }
        return true;
    }

    public BigInteger multiplicity(T t) {
        return innerMap.get(t) == null ? BigInteger.ZERO : innerMap.get(t);
    }

    // Do we want to make this change so it is immutable?
    public DafnyMultiset<T> update(T t, BigInteger b) {
        assert b != null && b.compareTo(BigInteger.ZERO) >= 0 : "Precondition Violation";
        HashMap<T, BigInteger> copy = new HashMap<>(innerMap);
        if (b.compareTo(BigInteger.ZERO) == 0) {
            copy.remove(t);
        } else {
            copy.put(t, b);
        }
        return new DafnyMultiset<>(copy);
    }

    public DafnyMultiset<T> union(DafnyMultiset<T> other) {
        assert other != null : "Precondition Violation";
        DafnyMultiset<T> u = new DafnyMultiset<>(innerMap);
        for (Map.Entry<T, BigInteger> entry : other.innerMap.entrySet()) {
            u.increment(entry.getKey(), entry.getValue());
        }
        return u;
    }

    // Returns a DafnyMultiSet with multiplicities that are
    // max(this.multiplicity(e)-other.multiplicity(e), BigInteger.ZERO)
    public DafnyMultiset<T> difference(DafnyMultiset<T> other) {
        assert other != null : "Precondition Violation";
        DafnyMultiset<T> u = new DafnyMultiset<>(innerMap);
        for (Map.Entry<T, BigInteger> entry : other.innerMap.entrySet()) {
            u.increment(entry.getKey(), entry.getValue().negate());
        }
        return u;
    }

    // Returns a DafnyMultiSet with multiplicities that are min(this.multiplicity(e), other.multiplicity(e))
    public DafnyMultiset<T> intersection(DafnyMultiset<T> other) {
        assert other != null : "Precondition Violation";
        DafnyMultiset<T> u = new DafnyMultiset<>();
        for (Map.Entry<T, BigInteger> entry : innerMap.entrySet()) {
            u = u.update(entry.getKey(), entry.getValue().min(other.multiplicity(entry.getKey())));
        }

        return u;
    }

    //adds n (possibly negative) to value of t. Removes if sum <= 0.
    public BigInteger increment(T t, BigInteger b) {
        assert b != null : "Precondition Violation";
        BigInteger n = b.negate().compareTo(multiplicity(t)) >= 0 ? BigInteger.ZERO : multiplicity(t).add(b);
        put(t, n);
        return n;
    }

    private void put(T t, BigInteger b){
        assert b != null && b.compareTo(BigInteger.ZERO) >= 0 : "Precondition Violation";
        if (b.compareTo(BigInteger.ZERO) == 0) {
            innerMap.remove(t);
        } else {
            innerMap.put(t, b);
        }
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
