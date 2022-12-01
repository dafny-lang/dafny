// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

package dafny;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Function;

import dafny.TypeDescriptor;

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
    public static <T> DafnySequence<T> of(TypeDescriptor<T> type, T ... elements) {
        Array<T> array;
        if (!type.isPrimitive()) {
            array = Array.wrap(type, elements.clone());
        } else {
            // Need to unbox each individual element.  Slow, but it should be
            // unusual to have a large sequence display of unknown type.
            array = Array.newArray(type, elements.length);
            for (int i = 0; i < elements.length; i++) {
                array.set(i, elements[i]);
            }
        }
        return DafnySequence.fromArray(type, array);
    }

    public static DafnySequence<Byte> of(byte ... elements) {
        return DafnySequence.fromArray(TypeDescriptor.BYTE, Array.wrap(elements));
    }

    public static DafnySequence<Short> of(short ... elements) {
        return DafnySequence.fromArray(TypeDescriptor.SHORT, Array.wrap(elements));
    }

    public static DafnySequence<Integer> of(int ... elements) {
        return DafnySequence.fromArray(TypeDescriptor.INT, Array.wrap(elements));
    }

    public static DafnySequence<Long> of(long ... elements) {
        return DafnySequence.fromArray(TypeDescriptor.LONG, Array.wrap(elements));
    }

    public static DafnySequence<Boolean> of(boolean ... elements) {
        return DafnySequence.fromArray(TypeDescriptor.BOOLEAN, Array.wrap(elements));
    }

    public static DafnySequence<Character> of(char ... elements) {
        return DafnySequence.fromArray(TypeDescriptor.CHAR, Array.wrap(elements));
    }

    @SuppressWarnings("unchecked")
    public static <T> DafnySequence<T> empty(TypeDescriptor<T> type) {
        if (type == TypeDescriptor.CHAR) {
            return (DafnySequence<T>) asString("");
        }
        return ArrayDafnySequence.<T> empty(type);
    }

    public static <T> DafnySequence<T> fromArray(TypeDescriptor<T> type, Array<T> elements) {
        return fromRawArray(type, elements.unwrap());
    }

    @SuppressWarnings("unchecked")
    public static <T> DafnySequence<T> fromRawArray(TypeDescriptor<T> type, Object elements) {
        if (type == TypeDescriptor.CHAR) {
            return (DafnySequence<T>) asString(new String((char[]) elements));
        }
        return new ArrayDafnySequence<>(Array.wrap(type, elements).copy());
    }

    /**
     * Return a sequence backed by the given array without making a defensive
     * copy.  Only safe if the array never changes afterward.
     */
    public static <T> DafnySequence<T> unsafeWrapArray(Array<T> elements) {
        return new ArrayDafnySequence<>(elements, true);
    }

    public static <T> DafnySequence<T> unsafeWrapRawArray(TypeDescriptor<T> type, Object elements) {
        return new ArrayDafnySequence<>(Array.wrap(type, elements));
    }

    public static <T> DafnySequence<T> fromArrayRange(TypeDescriptor<T> type, Array<T> elements, int lo, int hi) {
        return new ArrayDafnySequence<T>(elements.copyOfRange(lo, hi));
    }

    public static <T> DafnySequence<T> fromRawArrayRange(TypeDescriptor<T> type, Object elements, int lo, int hi) {
        return fromArrayRange(type, Array.wrap(type, elements), lo, hi);
    }

    public static <T> DafnySequence<T> fromList(TypeDescriptor<T> type, List<T> l) {
        assert l != null: "Precondition Violation";
        return new ArrayDafnySequence<T>(Array.fromList(type, l));
    }

    public static DafnySequence<Character> asString(String s){
        return new StringDafnySequence(s);
    }

    public static DafnySequence<CodePoint> asUnicodeString(String s) {
        int[] codePoints = new int[s.codePointCount(0, s.length())];
        int charIndex = 0;
        for (int codePointIndex = 0; codePointIndex < codePoints.length; codePointIndex++) {
            char c1 = s.charAt(charIndex++);
            if (Character.isHighSurrogate(c1)) {
                if (charIndex >= s.length()) {
                    throw new IllegalArgumentException();
                }
                char c2 = s.charAt(charIndex++);
                if (!Character.isLowSurrogate(c2)) {
                    throw new IllegalArgumentException();
                }
                codePoints[codePointIndex] = Character.toCodePoint(c1, c2);
            } else {
                codePoints[codePointIndex] = c1;
            }
        }
        return new ArrayDafnySequence<>(Array.wrap(TypeDescriptor.UNICODE_CHAR, codePoints));
    }

    public static DafnySequence<Byte> fromBytes(byte[] bytes) {
        return unsafeWrapBytes(bytes.clone());
    }

    /**
     * Return a sequence backed by the given byte array without making a
     * defensive copy.  Only safe if the array never changes afterward.
     */
    public static DafnySequence<Byte> unsafeWrapBytes(byte[] bytes) {
        return unsafeWrapArray(Array.wrap(bytes));
    }

    public static <T> DafnySequence<T> Create(TypeDescriptor<T> type, BigInteger length, Function<BigInteger, T> init) {
        int len = length.intValueExact();
        Array<T> values = Array.newArray(type, len);
        for(int i = 0; i < len; i++) {
            values.set(i, init.apply(BigInteger.valueOf(i)));
        }
        return fromArray(type, values);
    }

    @SuppressWarnings("unchecked")
    public static <T> TypeDescriptor<DafnySequence<? extends T>> _typeDescriptor(TypeDescriptor<T> elementType) {
        return TypeDescriptor.referenceWithDefault(
                (Class<DafnySequence<? extends T>>) (Class<?>) DafnySequence.class,
                DafnySequence.empty(elementType));
    }

    public Array<T> toArray() {
        return Array.fromList(elementType(), asList());
    }

    public Object toRawArray() {
        return toArray().unwrap();
    }

    public static byte[] toByteArray(DafnySequence<Byte> seq) {
        return Array.unwrapBytes(seq.toArray());
    }

    public static int[] toIntArray(DafnySequence<Integer> seq) {
        return Array.unwrapInts(seq.toArray());
    }

    public abstract TypeDescriptor<T> elementType();

    // Determines if this DafnySequence is a prefix of other
    public <U> boolean isPrefixOf(DafnySequence<U> other) {
        assert other != null : "Precondition Violation";
        if (other.length() < length()) return false;
        for (int i = 0; i < length(); i++) {
            if (!java.util.Objects.equals(this.select(i), other.select(i))) return false;
        }
        return true;
    }

    // Determines if this DafnySequence is a proper prefix of other
    public <U> boolean isProperPrefixOf(DafnySequence<U> other) {
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

    @SuppressWarnings("unchecked")
    public static <T> DafnySequence<T> concatenate(DafnySequence<? extends T> th, DafnySequence<? extends T> other) {
        assert th != null : "Precondition Violation";
        assert other != null : "Precondition Violation";

        if (th.isEmpty()) {
            return (DafnySequence<T>)other;
        } else if (other.isEmpty()) {
            return (DafnySequence<T>)th;
        } else {
            return new ConcatDafnySequence<T>((DafnySequence<T>)th, (DafnySequence<T>)other);
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

    public abstract <R> DafnySequence<R> update(int i, R t);

    public static <R> DafnySequence<R> update(DafnySequence<? extends R> seq, BigInteger b, R t) {
        return seq.<R>update(b.intValue(), t);
    }

    public static <R> DafnySequence<R> update(DafnySequence<? extends R> seq, int idx, R t) {
        return seq.<R>update(idx, t);
    }

    public static <R> DafnySequence<R> update(DafnySequence<? extends R> seq, long idx, R t) {
        return seq.<R>update((int)idx, t);
    }

    @SuppressWarnings("unchecked")
    public boolean contains(Object t) {
        assert t != null : "Precondition Violation";
        return asList().indexOf((T)t) != -1;
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

    public final DafnySequence<? extends DafnySequence<? extends T>> slice(List<Integer> l) {
        assert l != null : "Precondition Violation";
        ArrayList<DafnySequence<? extends T>> list = new ArrayList<>();
        int curr = 0;
        for (Integer i : l) {
            assert i != null : "Precondition Violation";
            list.add(subsequence(curr, curr + i));
            curr += i;
        }

        TypeDescriptor<T> eexx = elementType();
        TypeDescriptor<DafnySequence<? extends T>> ssxx = _typeDescriptor(eexx);
        return fromList(ssxx, list);
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
    public String verbatimString() {
        if (elementType() == TypeDescriptor.UNICODE_CHAR) {
            // This is slow, but the override in ArrayDafnySequence will almost
            // always be used instead
            int[] codePoints = new int[length()];
            int i = 0;
            for(Integer ch: (List<Integer>) asList())
            {
                codePoints[i++] = ch;
            }
            return new String(codePoints, 0, codePoints.length);
        } else {
            // This is slow, but the override in StringDafnySequence will almost
            // always be used instead
            StringBuilder builder = new StringBuilder(length());
            for(Character ch: (List<Character>) asList())
            {
                builder.append(ch);
            }
            return builder.toString();
        }
    }

    public Iterable<T> Elements() {
        return this;
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
    private final Array<T> seq;
    @SuppressWarnings("unused")
    private boolean unsafe; // for debugging purposes

    // NOTE: Input array is *shared*; must be a copy if it comes from a public input
    ArrayDafnySequence(TypeDescriptor<T> elementType, Object elements, boolean unsafe) {
        this(Array.wrap(elementType, elements), unsafe);
    }

    ArrayDafnySequence(TypeDescriptor<T> elementType, Object elements) {
        this(Array.wrap(elementType, elements));
    }

    ArrayDafnySequence(Array<T> elements, boolean unsafe) {
        this.seq = elements;
        this.unsafe = unsafe;
    }

    ArrayDafnySequence(Array<T> array) {
        this(array, false);
    }

    Array<T> unwrap() {
        return seq;
    }

    @Override
    public Array<T> toArray() {
        return seq.copy();
    }

    public static <T> ArrayDafnySequence<T> empty(TypeDescriptor<T> type) {
        return new ArrayDafnySequence<T>(type, type.newArray(0));
    }

    @Override
    public TypeDescriptor<T> elementType() {
        return seq.elementType();
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> ArrayDafnySequence<R> update(int i, R t) {
        assert t != null : "Precondition Violation";
        //todo: should we allow i=length, and return a new sequence with t appended to the sequence?
        assert 0 <= i && i < length(): "Precondition Violation";
        Array<R> newArray = (Array<R>)seq.copy();
        newArray.set(i, t);
        return new ArrayDafnySequence<>(newArray);
    }

    public ArrayDafnySequence<T> subsequence(int lo, int hi) {
        assert lo >= 0 && hi >= 0 && hi >= lo : "Precondition Violation";

        return new ArrayDafnySequence<>(seq.copyOfRange(lo, hi));
    }

    @Override
    Copier<T> newCopier(final int length) {
        return new Copier<T>() {
            private final Array<T> newArray = Array.newArray(seq.elementType(), length);
            private int nextIndex = 0;

            @Override
            public void copyFrom(DafnySequence<T> source) {
                source = source.force();
                if (source instanceof ArrayDafnySequence<?>) {
                    Array<T> sourceArray = ((ArrayDafnySequence<T>) source).seq;
                    sourceArray.copy(0, newArray, nextIndex, sourceArray.length());
                    nextIndex += sourceArray.length();
                } else {
                    for (T t : source) {
                        newArray.set(nextIndex++, t);
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
    protected List<T> asList() {
        return new AbstractList<T>() {
            @Override
            public T get(int index) {
                return seq.get(index);
            }

            @Override
            public T set(int index, T element) {
                T prev = seq.get(index);
                seq.set(index, element);
                return prev;
            }

            @Override
            public int size() {
                return length();
            }
        };
    }

    @Override
    public T select(int i) {
        return (T) seq.get(i);
    }

    @Override
    public int length() {
        return seq.length();
    }

    @Override
    public Iterator<T> iterator() {
        return asList().iterator();
    }

    @Override
    protected boolean equalsNonLazy(NonLazyDafnySequence<T> other) {
        if (other instanceof ArrayDafnySequence<?>) {
            return seq.deepEquals(((ArrayDafnySequence<T>) other).seq);
        } else {
            return super.equalsNonLazy(other);
        }
    }

    @Override
    public int hashCode() {
        return asList().hashCode();
    }

    @Override
    public String verbatimString() {
        if (elementType() == TypeDescriptor.UNICODE_CHAR) {
            return new String((int[]) seq.unwrap(), 0, seq.length());
        } else {
            return new String((char[]) seq.unwrap());
        }
    }
}

final class StringDafnySequence extends NonLazyDafnySequence<Character> {
    private final String string;

    StringDafnySequence(String string) {
        this.string = string;
    }

    @Override
    public Array<Character> toArray() {
        return Array.wrap(string.toCharArray());
    }

    @Override
    public TypeDescriptor<Character> elementType() {
        return TypeDescriptor.CHAR;
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
    @SuppressWarnings("unchecked")
    public <R> DafnySequence<R> update(int i, R t) {
        // assume R == Character
        assert t != null : "Precondition Violation";
        StringBuilder sb = new StringBuilder(string);
        sb.setCharAt(i, (Character)t);
        return (DafnySequence<R>)new StringDafnySequence(sb.toString());
    }

    @Override
    public boolean contains(Object t) {
        assert t != null : "Precondition Violation";
        return string.indexOf((Character)t) != -1;
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

    @Override
    public String toString() {
        return string;
    }
}

abstract class LazyDafnySequence<T> extends DafnySequence<T> {
    @Override
    public Array<T> toArray() {
        return force().toArray();
    }

    @Override
    public TypeDescriptor<T> elementType() {
        return force().elementType();
    }

    @Override
    protected List<T> asList() {
        return force().asList();
    }

    @Override
    public T select(int i) {
        return force().select(i);
    }

    @Override
    public int length() {
        return force().length();
    }

    @Override
    public <R> DafnySequence<R> update(int i, R t) {
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
    public String toString() {
        return force().toString();
    }

    @Override
    public String verbatimString() {
        return force().verbatimString();
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
        // sequence.  This is fine unless native Java code is uncareful and has
        // has created ArrayDafnySequences of boxed primitive types.
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
