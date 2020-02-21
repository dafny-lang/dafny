package dafny;

import java.lang.reflect.Array;
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

    /**
     * Return a sequence backed by the given array without making a defensive
     * copy.  Only safe if the array never changes afterward.
     */
    public static <T> DafnySequence<T> unsafeWrapArray(T[] elements) {
        return new ArrayDafnySequence<>(elements, true);
    }

    public static <T> DafnySequence<T> fromArrayRange(T[] elements, int lo, int hi) {
        return new ArrayDafnySequence<T>(Arrays.copyOfRange(elements, lo, hi));
    }

    public static <T> DafnySequence<T> fromList(List<T> l) {
        assert l != null: "Precondition Violation";
        return new ArrayDafnySequence<T>(l.toArray());
    }

    public static DafnySequence<Character> asString(String s){
        return new StringDafnySequence(s);
    }

    public static DafnySequence<Byte> fromBytes(byte[] bytes) {
        return new ByteArrayDafnySequence(bytes.clone());
    }

    /**
     * Return a sequence backed by the given byte array without making a
     * defensive copy.  Only safe if the array never changes afterward.
     */
    public static DafnySequence<Byte> unsafeWrapBytes(byte[] bytes) {
        return new ByteArrayDafnySequence(bytes);
    }

    /**
     * Return a sequence backed by the given byte array without making a
     * defensive copy.  Only safe if the array never changes afterward.
     */
    public static DafnySequence<Byte> unsafeWrapBytes(byte[] bytes) {
        return new ByteArrayDafnySequence(bytes);
    }

    public static <T> DafnySequence<T> Create(BigInteger length, Function<BigInteger, T> init) {
        // TODO This could try and create a ByteArrayDafnySequence or StringDafnySequence if possible
        Object[] values = new Object[length.intValueExact()];
        for(BigInteger i = BigInteger.ZERO; i.compareTo(length) < 0; i = i.add(BigInteger.ONE)) {
            values[i.intValueExact()] = init.apply(i);
        }
        return new ArrayDafnySequence<>(values);
    }

    @SuppressWarnings("unchecked")
    public T[] toArray(Class<T> type) {
        return asList().toArray((T[]) Array.newInstance(type, 0));
    }

    public static byte[] toByteArray(DafnySequence<Byte> seq) {
        seq = seq.force();
        if (seq instanceof ByteArrayDafnySequence) {
            return ((ByteArrayDafnySequence) seq).array.clone();
        } else {
            byte[] ans = new byte[seq.length()];
            int i = 0;
            for (Byte b : seq) {
                ans[i++] = b;
            }
            return ans;
        }
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

        public NonLazyDafnySequence<T> result();
    }

    public abstract T select(int i);

    public T selectUnsigned(byte i) {
        return select(Byte.toUnsignedInt(i));
    }

    public T selectUnsigned(short i) {
        return select(Short.toUnsignedInt(i));
    }

    public T selectUnsigned(int i) {
        return select(Integer.toUnsignedLong(i));
    }

    public T select(long i) {
        return select(BigInteger.valueOf(i));
    }

    public T selectUnsigned(long i) {
        return select(Helpers.unsignedLongToBigInteger(i));
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

    public DafnySequence<T> dropUnsigned(byte lo) {
        return drop(Byte.toUnsignedInt(lo));
    }

    public DafnySequence<T> dropUnsigned(short lo) {
        return drop(Short.toUnsignedInt(lo));
    }

    public DafnySequence<T> dropUnsigned(int lo) {
        return drop(Integer.toUnsignedLong(lo));
    }

    public DafnySequence<T> drop(long lo) {
        return drop(BigInteger.valueOf(lo));
    }

    public DafnySequence<T> dropUnsigned(long lo) {
        return drop(Helpers.unsignedLongToBigInteger(lo));
    }

    public DafnySequence<T> drop(BigInteger lo) {
        return drop(lo.intValue());
    }


    // Returns the subsequence of values [0..hi)
    public final DafnySequence<T> take(int hi) {
        assert hi >= 0 && hi <= length() : "Precondition Violation";
        return subsequence(0, hi);
    }

    public DafnySequence<T> takeUnsigned(byte hi) {
        return take(Byte.toUnsignedInt(hi));
    }

    public DafnySequence<T> takeUnsigned(short hi) {
        return take(Short.toUnsignedInt(hi));
    }

    public DafnySequence<T> takeUnsigned(int hi) {
        return take(Integer.toUnsignedLong(hi));
    }

    public DafnySequence<T> take(long hi) {
        return take(BigInteger.valueOf(hi));
    }

    public DafnySequence<T> takeUnsigned(long hi) {
        return take(Helpers.unsignedLongToBigInteger(hi));
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
    public final boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof DafnySequence<?>)) {
            return false;
        }
        @SuppressWarnings("unchecked")
        DafnySequence<T> other = (DafnySequence<T>) obj;
        return this.equalsNonLazy(other.force());
    }

    /**
     * Compare for equality to the given sequence, assuming that it is not
     * null, not == to this, and not lazy.
     */
    protected boolean equalsNonLazy(NonLazyDafnySequence<T> other) {
        return asList().equals(other.asList());
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

    /**
     * @return The sequence representing this sequence's actual value.
     * That's usually just the sequence itself, but not if the
     * sequence is lazily computed.
     *
     * @see ConcatDafnySequence
     */
    protected abstract NonLazyDafnySequence<T> force();
}

abstract class NonLazyDafnySequence<T> extends DafnySequence<T> {
    @Override
    protected final NonLazyDafnySequence<T> force() {
        return this;
    }
}

final class ArrayDafnySequence<T> extends NonLazyDafnySequence<T> {
    // not T[] because generics and arrays don't mix
    private Object[] seq;
    @SuppressWarnings("unused")
    private boolean unsafe; // for debugging purposes

    // NOTE: Input array is *shared*; must be a copy if it comes from a public input
    ArrayDafnySequence(Object[] elements, boolean unsafe) {
        this.seq = elements;
        this.unsafe = unsafe;
    }

    ArrayDafnySequence(Object[] elements) {
        this(elements, false);
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
                source = source.force();
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
            public NonLazyDafnySequence<T> result() {
                return new ArrayDafnySequence<T>(newArray);
            }
        };
    }

    @Override
    @SuppressWarnings("unchecked")
    protected List<T> asList() {
        return (List<T>) Arrays.asList(seq);
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
    protected boolean equalsNonLazy(NonLazyDafnySequence<T> other) {
        if (other instanceof ArrayDafnySequence<?>) {
            return Arrays.equals(seq, ((ArrayDafnySequence<T>) other).seq);
        } else {
            return super.equalsNonLazy(other);
        }
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(seq);
    }
}

final class ByteArrayDafnySequence extends NonLazyDafnySequence<Byte> {
    final byte[] array;

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
                source = source.force();
                if (source instanceof ByteArrayDafnySequence) {
                    byte[] sourceArray = ((ByteArrayDafnySequence) source).array;
                    System.arraycopy(sourceArray, 0, newArray, nextIndex, sourceArray.length);
                    nextIndex += sourceArray.length;
                } else {
                    for (Byte t : source) {
                        newArray[nextIndex++] = t;
                    }
                }
            }

            @Override
            public NonLazyDafnySequence<Byte> result() {
                return new ByteArrayDafnySequence(newArray);
            }
        };
    }

    @Override
    public Iterator<Byte> iterator() {
        return new Iterator<Byte>() {
            private final int n = array.length;
            private int i = 0;

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
    public boolean equalsNonLazy(NonLazyDafnySequence<Byte> obj) {
        if (obj instanceof ByteArrayDafnySequence) {
            return Arrays.equals(array, ((ByteArrayDafnySequence) obj).array);
        } else {
            return super.equalsNonLazy(obj);
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

final class StringDafnySequence extends NonLazyDafnySequence<Character> {
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
                source = source.force();
                if (source instanceof StringDafnySequence) {
                    sb.append(((StringDafnySequence) source).string);
                } else {
                    for (char c : source) {
                        sb.append(c);
                    }
                }
            }

            @Override
            public NonLazyDafnySequence<Character> result() {
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
    public boolean equalsNonLazy(NonLazyDafnySequence<Character> obj) {
        if (obj instanceof StringDafnySequence) {
            return string.equals(((StringDafnySequence) obj).string);
        } else {
            return super.equalsNonLazy(obj);
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

abstract class LazyDafnySequence<T> extends DafnySequence<T> {
    @Override
    public T select(int i) {
        return force().select(i);
    }

    @Override
    public int length() {
        return force().length();
    }

    @Override
    public DafnySequence<T> update(int i, T t) {
        return force().update(i, t);
    }

    @Override
    public DafnySequence<T> subsequence(int lo, int hi) {
        return force().subsequence(lo, hi);
    }

    @Override
    Copier<T> newCopier(int length) {
        return force().newCopier(length);
    }

    @Override
    public Iterator<T> iterator() {
        return force().iterator();
    }

    @Override
    protected boolean equalsNonLazy(NonLazyDafnySequence<T> other) {
        return force().equalsNonLazy(other);
    }

    @Override
    public int hashCode() {
        return force().hashCode();
    }
}

final class ConcatDafnySequence<T> extends LazyDafnySequence<T> {
    // INVARIANT: Either these are both non-null and ans is null or both are
    // null and ans is non-null.
    private DafnySequence<T> left, right;
    // XXX We're storing the combined sequence as a DafnySequence, not an array,
    // because it might need a backing array of primitive type.  Unfortunately,
    // this means the resulting sequence is doomed to have a bit of overhead (an
    // extra indirect function call) on every call to select().  Hard to see how
    // to fix this without requiring that *every* DafnySequence suffer some
    // overhead.
    private NonLazyDafnySequence<T> ans = null;
    private final int length;

    ConcatDafnySequence(DafnySequence<T> left, DafnySequence<T> right) {
        this.left = left;
        this.right = right;
        this.length = left.length() + right.length();
    }

    @Override
    protected NonLazyDafnySequence<T> force() {
        if (ans == null) {
            ans = computeElements();
            // Allow left and right to be garbage-collected
            left = null;
            right = null;
        }

        return ans;
    }

    @Override
    public int length() {
        return length;
    }

    private NonLazyDafnySequence<T> computeElements() {
        // Somewhat arbitrarily, the copier will be created by the leftmost
        // sequence.  TODO: Have enough run-time type information that this is
        // less fallible.  In particular, the left-most sequence might
        // unluckily be an ArrayDafnySequence for a boxed type, which would be a
        // disaster if the other sequences are of a specialized subclass.
        // Without passing around type descriptors, we can't avoid this.
        Copier<T> copier;

        // Treat this instance as the root of a tree, where a
        // ConcatDafnySequence is an internal node (with its left and right
        // fields as children) and any other DafnySequence is a leaf node,
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
