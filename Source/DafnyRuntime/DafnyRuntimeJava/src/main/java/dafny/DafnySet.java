package dafny;

import java.util.*;

// A class that is equivalent to the implementation of Set in Dafny
public class DafnySet<T> {
    private Set<T> innerSet;

    public DafnySet() {
        innerSet = new HashSet<>();
    }

    public DafnySet(Set<T> s) {
        assert s != null : "Precondition Violation";
        innerSet = new HashSet<>(s);
    }

    public DafnySet(Collection<T> c) {
        assert c != null : "Precondition Violation";
        innerSet = new HashSet<>(c);
    }

    public DafnySet(DafnySet<T> other) {
        assert other != null : "Precondition Violation";
        innerSet = new HashSet<>(other.innerSet);
    }

    public DafnySet(List<T> l) {
        assert l != null : "Precondition Violation";
        innerSet = new HashSet<>(l);
    }

    @SafeVarargs
    public static <T> DafnySet<T> of(T ... elements) {
        return new DafnySet<T>(Arrays.asList(elements));
    }

    private static final DafnySet<Object> EMPTY = DafnySet.of();

    @SuppressWarnings("unchecked")
    public static <T> DafnySet<T> empty() {
        // Safe because immutable
        return (DafnySet<T>) EMPTY;
    }

    @SuppressWarnings("unchecked")
    public static <T> Type<DafnySet<? extends T>> _type(Type<T> elementType) {
        // Fudge the type parameter; it's not great, but it's safe because
        // (for now) type descriptors are only used for default values
        return Type.referenceWithDefault(
                (Class<DafnySet<? extends T>>) (Class<?>) DafnySet.class,
                DafnySet.empty());
    }

    // Determines if the current object is a subset of the DafnySet passed in. Requires that the input DafnySet is not
    // null.
    public boolean isSubsetOf(DafnySet other) {
        assert other != null : "Precondition Violation";
        return other.containsAll(this);
    }

    // Determines if the current object is a proper subset of the DafnySet passed in. Requires that the input DafnySet
    // is not null.
    public boolean isProperSubsetOf(DafnySet other) {
        assert other != null : "Precondition Violation";
        return isSubsetOf(other) && size() < other.size();
    }

    public boolean contains(Object t) {
        assert t != null : "Precondition Violation";
        return innerSet.contains(t);
    }

    public <U> boolean disjoint(DafnySet<? extends U> other) {
        assert other != null : "Precondition Violation";
        for (U u : other.innerSet) {
            if (contains(u)) return false;
        }
        return true;
    }

    public static <T> DafnySet<T> union(DafnySet<? extends T> th, DafnySet<? extends T> other) {
        assert th != null : "Precondition Violation";
        assert other != null : "Precondition Violation";

        if (th.isEmpty()) {
            return (DafnySet<T>)other;
        } else if (other.isEmpty()) {
            return (DafnySet<T>)th;
        } else {
            DafnySet<T> u = new DafnySet<T>((DafnySet<T>)other);
            u.addAll((DafnySet<T>)th);
            return u;
        }
    }

    //Returns a DafnySet containing elements only found in the current DafnySet
    public static <T> DafnySet<T> difference(DafnySet<? extends T> th, DafnySet<? extends T> other) {
        assert th != null : "Precondition Violation";
        assert other != null : "Precondition Violation";
        DafnySet<T> u = new DafnySet<T>((DafnySet<T>)th);
        u.removeAll((DafnySet<T>)other);
        return u;
    }

    public static <T> DafnySet<T> intersection(DafnySet<? extends T> th, DafnySet<? extends T> other) {
        assert th != null : "Precondition Violation";
        assert other != null : "Precondition Violation";
        DafnySet<T> u = new DafnySet<T>();
        for (T ele : th.innerSet) {
            if (other.contains(ele)) u.add(ele);
        }
        return u;
    }

    public boolean containsAll(DafnySet other) {
        assert other != null : "Precondition Violation";
        return innerSet.containsAll(other.innerSet);
    }

    public int size() {
        return innerSet.size();
    }

    public int cardinalityInt() {
        return size();
    }

    public boolean isEmpty() {
        return innerSet.isEmpty();
    }

    public boolean add(T t) {
        assert t != null : "Precondition Violation";
        return innerSet.add(t);
    }

    public boolean remove(T t) {
        assert t != null : "Precondition Violation";
        return innerSet.remove(t);
    }

    public boolean removeAll(DafnySet<T> other) {
        assert other != null : "Precondition Violation";
        return innerSet.removeAll(other.innerSet);
    }

    public boolean addAll(DafnySet<T> other) {
        assert other != null : "Precondition Violation";
        return innerSet.addAll(other.innerSet);
    }

    public Collection<DafnySet<T>> AllSubsets(){
        // Start by putting all set elements into a list, but don't include null
        List<T> elmts = new ArrayList<>();
        elmts.addAll(innerSet);
        int n = elmts.size();
        DafnySet<T> s;
        HashSet<DafnySet<T>> r = new HashSet<>();
        for (int i = 0; i < (1<<n); i++)
        {
            s = new DafnySet<>();
            int m = 1; // m is used to check set bit in binary representation.
            // Print current subset
            for (int j = 0; j < n; j++, m = m << 1)
            {
                if ((i & m) > 0)
                {
                    s.add(elmts.get(j));
                }
            }
            r.add(s);
        }
        return r;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnySet o = (DafnySet) obj;
        return containsAll(o) && o.containsAll(this);
    }

    @Override
    public int hashCode() {
        return innerSet.hashCode();
    }

    @Override
    public String toString() {
        String s = "{";
        String sep = "";
        for (T elem : innerSet) {
            s += sep + Helpers.toString(elem);
            sep = ", ";
        }
        return s + "}";
    }

    public DafnyMultiset<T> asDafnyMultiset() {
        return new DafnyMultiset<>(innerSet);
    }

    public Set<T> Elements() {
        return innerSet;
    }
}
