package dafny;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Function;

public abstract class DafnySequence<T> implements Iterable<T> {
    /*
    Invariant: forall 0<=i<length(). seq[i] == T || null
    Property: DafnySequences are immutable. Any methods that seem to edit the DafnySequence will only return a new
    DafnySequence
    Todo: DafnySequence Invariants and Properties
     */

    // Only allow subclasses in this package
    DafnySequence() { }

    @SafeVarargs
    public static <T> DafnySequence<T> of(T ... elements) {
        return DafnySequence.fromArray(elements);
    }

    public static <T> DafnySequence<T> empty() {
        return ArrayDafnySequence.<T> empty();
    }

    public static <T> DafnySequence<T> fromArray(T[] elements) {
        return new ArrayDafnySequence<>(elements.clone());
    }

    public static <T> DafnySequence<T> fromArrayRange(T[] elements, int lo, int hi) {
        return new ArrayDafnySequence<T>(Arrays.copyOfRange(elements, lo, hi));
    }

    public static <T> DafnySequence<T> fromList(List<T> l) {
        assert l != null: "Precondition Violation";
        return new ArrayDafnySequence<T>(l.toArray());
    }

    // XXX Shouldn't this be fromString()???
    public static DafnySequence<Character> asString(String s){
        return new StringDafnySequence(s);
    }

    public static DafnySequence<Byte> fromBytes(byte[] bytes) {
        return new ByteArrayDafnySequence(bytes.clone());
    }

    public static <T> DafnySequence<T> Create(BigInteger length, Function<BigInteger, T> init) {
        // TODO This could try and create a ByteArrayDafnySequence or StringDafnySequence if possible
        Object[] values = new Object[length.intValueExact()];
        for(BigInteger i = BigInteger.ZERO; i.compareTo(length) < 0; i = i.add(BigInteger.ONE)) {
            values[i.intValueExact()] = init.apply(i);
        }
        return new ArrayDafnySequence<>(values);
    }

    // Determines if this DafnySequence is a prefix of other
    public boolean isPrefixOf(DafnySequence<T> other) {
        assert other != null : "Precondition Violation";
        if (other.length() < length()) return false;
        for (int i = 0; i < length(); i++) {
            if (this.select(i) != other.select(i)) return false;
        }

        return true;
    }

    // Determines if this DafnySequence is a proper prefix of other
    public boolean isProperPrefixOf(DafnySequence<T> other) {
        assert other != null : "Precondition Violation";
        return length() < other.length() && isPrefixOf(other);
    }

    // This is just a convenience to implement infrequently-used operations or
    // non-performance-critical operations.  Uses of it may be specialized in
    // subclasses as needed.
    protected List<T> asList() {
        return new AbstractList<T>() {
            @Override
            public T get(int index) {
                return select(index);
            }

            @Override
            public int size() {
                return length();
            }

            @Override
            public Iterator<T> iterator() {
                return DafnySequence.this.iterator();
            }
        };
    }

    public final DafnySequence<T> concatenate(DafnySequence<T> other) {
        assert other != null : "Precondition Violation";

        if (this.isEmpty()) {
            return other;
        } else if (other.isEmpty()) {
            return this;
        } else {
            return new ConcatDafnySequence<T>(this, other);
        }
    }

    /**
     * Build a new sequence of the same type, and a known length, by copying
     * from a number of existing ones.
     *
     * Not public; only meant to be used by {@link ConcatDafnySequence}.
     */
    abstract Copier<T> newCopier(int length);

    /** @see #newCopier(int) */
    interface Copier<T> {
        public void copyFrom(DafnySequence<T> source);

        public DafnySequence<T> result();
    }

    public abstract T select(int i);

    public T select(UByte i) {
        return select(i.intValue());
    }

    public T select(UShort i) {
        return select(i.intValue());
    }

    public T select(UInt i) {
        return select(i.asBigInteger());
    }

    public T select(long i) {
        return select(BigInteger.valueOf(i));
    }

    public T select(ULong i) {
        return select(i.asBigInteger());
    }

    public T select(BigInteger i) {
        return select(i.intValue());
    }

    public abstract int length();

    public boolean isEmpty() {
        return this.length() == 0;
    }

    public final int cardinalityInt() {
        return length();
    }

    public abstract DafnySequence<T> update(int i, T t);

    public DafnySequence<T> update(BigInteger b, T t) {
        assert t != null : "Precondition Violation";
        assert b != null : "Precondition Violation";
        //todo: should we allow i=length, and return a new sequence with t appended to the sequence?
        assert b.compareTo(BigInteger.ZERO) >= 0 &&
               b.compareTo(BigInteger.valueOf(length())) < 0: "Precondition Violation";
        return update(b.intValue(), t);
    }

    public boolean contains(T t) {
        assert t != null : "Precondition Violation";
        return asList().indexOf(t) != -1;
    }

    // Returns the subsequence of values [lo..hi)
    public abstract DafnySequence<T> subsequence(int lo, int hi);


    // Returns the subsequence of values [lo..length())
    public final DafnySequence<T> drop(int lo) {
        assert lo >= 0 && lo <= length() : "Precondition Violation";
        return subsequence(lo, length());
    }

    public DafnySequence<T> drop(UByte lo) {
        return drop(lo.intValue());
    }

    public DafnySequence<T> drop(UShort lo) {
        return drop(lo.intValue());
    }

    public DafnySequence<T> drop(UInt lo) {
        return drop(lo.asBigInteger());
    }

    public DafnySequence<T> drop(long lo) {
        return drop(BigInteger.valueOf(lo));
    }

    public DafnySequence<T> drop(ULong lo) {
        return drop(lo.asBigInteger());
    }

    public DafnySequence<T> drop(BigInteger lo) {
        return drop(lo.intValue());
    }


    // Returns the subsequence of values [0..hi)
    public final DafnySequence<T> take(int hi) {
        assert hi >= 0 && hi <= length() : "Precondition Violation";
        return subsequence(0, hi);
    }

    public DafnySequence<T> take(UByte hi) {
        return take(hi.intValue());
    }

    public DafnySequence<T> take(UShort hi) {
        return take(hi.intValue());
    }

    public DafnySequence<T> take(UInt hi) {
        return take(hi.asBigInteger());
    }

    public DafnySequence<T> take(long hi) {
        return take(BigInteger.valueOf(hi));
    }

    public DafnySequence<T> take(ULong hi) {
        return take(hi.asBigInteger());
    }

    public DafnySequence<T> take(BigInteger hi) {
        return take(hi.intValue());
    }

    public final DafnySequence<DafnySequence<T>> slice(List<Integer> l) {
        assert l != null : "Precondition Violation";
        ArrayList<DafnySequence<T>> list = new ArrayList<>();
        int curr = 0;
        for (Integer i : l) {
            assert i != null : "Precondition Violation";
            list.add(subsequence(curr, curr + i));
            curr += i;
        }

        return new ArrayDafnySequence<>(list.toArray());
    }

    public DafnyMultiset<T> asDafnyMultiset() {
        return new DafnyMultiset<>(asList());
    }

    @Override
    public abstract Iterator<T> iterator();

    @Override
    public Spliterator<T> spliterator() {
        // TODO Override these with faster versions in subclasses if needed
        return asList().spliterator();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof DafnySequence<?>)) return false;
        DafnySequence<?> o = (DafnySequence<?>) obj;
        return asList().equals(o.asList());
    }

    @Override
    public abstract int hashCode();

    @Override
    public String toString() {
        return asList().toString();
    }

    @SuppressWarnings("unchecked")
    public String verbatimString(){
        // This is slow, but the override in StringDafnySequence will almost
        // always be used instead
        StringBuilder builder = new StringBuilder(length());
        for(Character ch: (List<Character>) asList())
        {
            builder.append(ch);
        }
        return builder.toString();
    }

    public HashSet<T> UniqueElements() {
        return new HashSet<>(asList());
    }
}

final class ArrayDafnySequence<T> extends DafnySequence<T> {
    // not T[] because generics and arrays don't mix
    private Object[] seq;

    // NOTE: Input array is *shared*; must be a copy if it comes from a public input
    ArrayDafnySequence(Object[] elements) {
        this.seq = elements;
    }

    private static final ArrayDafnySequence<Object> EMPTY =
        new ArrayDafnySequence<>(new Object[0]);

    @SuppressWarnings("unchecked")
    public static <T> ArrayDafnySequence<T> empty() {
        // Safe because immutable
        return (ArrayDafnySequence<T>) EMPTY;
    }

    @Override
    public ArrayDafnySequence<T> update(int i, T t) {
        assert t != null : "Precondition Violation";
        //todo: should we allow i=length, and return a new sequence with t appended to the sequence?
        assert 0 <= i && i < length(): "Precondition Violation";
        Object[] newArray = seq.clone();
        newArray[i] = t;
        return new ArrayDafnySequence<>(newArray);
    }

    public ArrayDafnySequence<T> subsequence(int lo, int hi) {
        assert lo >= 0 && hi >= 0 && hi >= lo : "Precondition Violation";

        return new ArrayDafnySequence<>(Arrays.copyOfRange(seq, lo, hi));
    }

    @Override
    Copier<T> newCopier(final int length) {
        return new Copier<T>() {
            private final Object[] newArray = new Object[length];
            private int nextIndex = 0;

            @Override
            public void copyFrom(DafnySequence<T> source) {
                if (source instanceof ArrayDafnySequence<?>) {
                    Object[] sourceArray = ((ArrayDafnySequence<?>) source).seq;
                    System.arraycopy(sourceArray, 0, newArray, nextIndex, sourceArray.length);
                    nextIndex += sourceArray.length;
                } else {
                    for (T t : source) {
                        newArray[nextIndex++] = t;
                    }
                }
            }

            @Override
            public DafnySequence<T> result() {
                return new ArrayDafnySequence<T>(newArray);
            }
        };
    }

    @Override
    @SuppressWarnings("unchecked")
    protected List<T> asList() {
        return (List) Arrays.asList(seq);
    }

    @Override
    @SuppressWarnings("unchecked")
    public T select(int i) {
        return (T) seq[i];
    }

    @Override
    public int length() {
        return seq.length;
    }

    @Override
    public Iterator<T> iterator() {
        return asList().iterator();
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(seq);
    }
}

final class ByteArrayDafnySequence extends DafnySequence<Byte> {
    private final byte[] array;

    // NOTE: Input array is *shared*; must be a copy if it comes from a public input
    ByteArrayDafnySequence(byte[] elements) {
        this.array = elements;
    }

    @Override
    public Byte select(int i) {
        return array[i];
    }

    @Override
    public int length() {
        return array.length;
    }

    @Override
    public DafnySequence<Byte> update(int i, Byte t) {
        byte[] newArray = array.clone();
        newArray[i] = t;
        return new ByteArrayDafnySequence(newArray);
    }

    @Override
    public DafnySequence<Byte> subsequence(int lo, int hi) {
        // XXX Share rather than copy?
        return new ByteArrayDafnySequence(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    Copier<Byte> newCopier(int length) {
        return new Copier<Byte>() {
            private final byte[] newArray = new byte[length];
            private int nextIndex = 0;

            @Override
            public void copyFrom(DafnySequence<Byte> source) {
                if (source instanceof ByteArrayDafnySequence) {
                    byte[] sourceArray = ((ByteArrayDafnySequence) source).array;
                    System.arraycopy(sourceArray, 0, newArray, nextIndex, sourceArray.length);
                    nextIndex += sourceArray.length;
                } else {
                    for (byte b : source) {
                        newArray[nextIndex++] = b;
                    }
                }
            }

            @Override
            public DafnySequence<Byte> result() {
                return new ByteArrayDafnySequence(newArray);
            }
        };
    }

    @Override
    public Iterator<Byte> iterator() {
        final int n = array.length;

        return new Iterator<Byte>() {
            int i = 0;

            @Override
            public boolean hasNext() {
                return i < n;
            }

            @Override
            public Byte next() {
                return array[i++];
            }
        };
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof ByteArrayDafnySequence) {
            return Arrays.equals(array, ((ByteArrayDafnySequence) obj).array);
        } else {
            return super.equals(obj);
        }
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(array);
    }

    @Override
    public String toString() {
        return Arrays.toString(array);
    }
}

final class StringDafnySequence extends DafnySequence<Character> {
    private final String string;

    StringDafnySequence(String string) {
        this.string = string;
    }

    @Override
    public Character select(int i) {
        return string.charAt(i);
    }

    @Override
    public int length() {
        return string.length();
    }

    @Override
    public DafnySequence<Character> update(int i, Character t) {
        assert t != null : "Precondition Violation";
        StringBuilder sb = new StringBuilder(string);
        sb.setCharAt(i, t);
        return new StringDafnySequence(sb.toString());
    }

    @Override
    public boolean contains(Character t) {
        assert t != null : "Precondition Violation";
        return string.indexOf(t) != -1;
    }

    @Override
    public DafnySequence<Character> subsequence(int lo, int hi) {
        return new StringDafnySequence(string.substring(lo, hi));
    }

    @Override
    Copier<Character> newCopier(int length) {
        return new Copier<Character>() {
            private final StringBuilder sb = new StringBuilder(length);

            @Override
            public void copyFrom(DafnySequence<Character> source) {
                if (source instanceof StringDafnySequence) {
                    sb.append(((StringDafnySequence) source).string);
                } else {
                    for (char c : source) {
                        sb.append(c);
                    }
                }
            }

            @Override
            public DafnySequence<Character> result() {
                return new StringDafnySequence(sb.toString());
            }
        };
    }

    @Override
    public Iterator<Character> iterator() {
        final int n = string.length();
        return new Iterator<Character>() {
            int i = 0;

            @Override
            public boolean hasNext() {
                return i < n;
            }

            @Override
            public Character next() {
                return string.charAt(i++);
            }
        };
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof StringDafnySequence) {
            return string.equals(((StringDafnySequence) obj).string);
        } else {
            return super.equals(obj);
        }
    }

    @Override
    public int hashCode() {
        return string.hashCode();
    }

    @Override
    public String verbatimString() {
        return string;
    }
}

final class ConcatDafnySequence<T> extends DafnySequence<T> {
    // INVARIANT: Either these are both non-null and ans is null or both are
    // null and ans is non-null.
    private DafnySequence<T> left, right;
    // XXX We're storing the combined sequence as a DafnySequence, not an array,
    // because it might need a backing array of primitive type.  Unfortunately,
    // this means the resulting sequence is doomed to have a bit of overhead (an
    // extra indirect function call) on every call to select().  Hard to see how
    // to fix this without requiring that *every* DafnySequence suffer some
    // overhead.
    private DafnySequence<T> ans = null;
    private final int length;

    ConcatDafnySequence(DafnySequence<T> left, DafnySequence<T> right) {
        this.left = left;
        this.right = right;
        this.length = left.length() + right.length();
    }

    private DafnySequence<T> resolve() {
        if (ans == null) {
            ans = computeElements();
            // Allow left and right to be garbage-collected
            left = null;
            right = null;
        }

        return ans;
    }

    @Override
    public T select(int i) {
        return resolve().select(i);
    }

    @Override
    public int length() {
        return length;
    }

    @Override
    public DafnySequence<T> update(int i, T t) {
        return resolve().update(i, t);
    }

    @Override
    public DafnySequence<T> subsequence(int lo, int hi) {
        return resolve().subsequence(lo, hi);
    }

    @Override
    Copier<T> newCopier(int length) {
        return resolve().newCopier(length);
    }

    @Override
    public Iterator<T> iterator() {
        return resolve().iterator();
    }

    @Override
    public int hashCode() {
        return resolve().hashCode();
    }

    private DafnySequence<T> computeElements() {
        // Somewhat arbitrarily, the copier will be created by the leftmost
        // sequence.  TODO: Have enough run-time type information that this is
        // less fallible.  In particular, the left-most sequence might
        // unluckily be an ArrayDafnySequence for a boxed type, which would be a
        // disaster if the other sequences are of a specialized subclass.
        // Without passing around type descriptors, we can't avoid this.
        Copier<T> copier;

        // Treat this instance as the root of a tree, where a
        // ConcatDafnySequence is an internal node (with its left and right
        // fields as children) and any other ConcatDafnySequence is a leaf node,
        // and prepare to perform a non-recursive in-order traversal.  (We could
        // use recursion, but there could easily be enough sequences being
        // concatenated to exhaust the system stack.)
        Deque<DafnySequence<T>> toVisit = new ArrayDeque<>();

        toVisit.push(right);
        DafnySequence<T> first = left;
        while (first instanceof ConcatDafnySequence<?> &&
                ((ConcatDafnySequence<T>) first).ans == null) {
            toVisit.push(((ConcatDafnySequence<T>) first).right);
            first = ((ConcatDafnySequence<T>) first).left;
        }
        toVisit.push(first);

        copier = first.newCopier(this.length);

        while (!toVisit.isEmpty()) {
            DafnySequence<T> seq = toVisit.pop();

            if (seq instanceof ConcatDafnySequence<?>) {
                ConcatDafnySequence<T> cseq = (ConcatDafnySequence<T>) seq;

                if (cseq.ans != null) {
                    copier.copyFrom(cseq.ans);
                } else {
                    toVisit.push(cseq.right);
                    toVisit.push(cseq.left);
                }
            } else {
                copier.copyFrom(seq);
            }
        }

        return copier.result();
    }
}