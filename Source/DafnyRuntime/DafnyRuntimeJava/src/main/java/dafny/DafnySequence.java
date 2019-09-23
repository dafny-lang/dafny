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
        return new ArrayDafnySequence<T>(elements.clone());
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

    public DafnySequence<T> concatenate(DafnySequence<T> other) {
        assert other != null : "Precondition Violation";
        Object[] newArray = new Object[this.length() + other.length()];
        int i = 0;
        for (T t : this) {
            newArray[i++] = t;
        }
        for (T t : other) {
            newArray[i++] = t;
        }
        return new ArrayDafnySequence<>(newArray);
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

    public abstract DafnySequence<T> update(int i, T t);

    public DafnySequence<T> update(BigInteger b, T t) {
        //todo: should we allow i=length, and return a new sequence with t appended to the sequence?
        assert b.compareTo(BigInteger.ZERO) >= 0 &&
               b.compareTo(BigInteger.valueOf(length())) < 0: "Precondition Violation";
        return update(b.intValue(), t);
    }

    public boolean contains(T t) {
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
        new ArrayDafnySequence<Object>(new Object[0]);

    @SuppressWarnings("unchecked")
    public static <T> ArrayDafnySequence<T> empty() {
        // Safe because immutable
        return (ArrayDafnySequence<T>) EMPTY;
    }

    @Override
    public ArrayDafnySequence<T> update(int i, T t) {
        //todo: should we allow i=length, and return a new sequence with t appended to the sequence?
        assert 0 <= i && i < length(): "Precondition Violation";
        Object[] newArray = seq.clone();
        newArray[i] = t;
        return new ArrayDafnySequence<T>(newArray);
    }

    public ArrayDafnySequence<T> subsequence(int lo, int hi) {
        assert lo >= 0 && hi >= 0 && hi >= lo : "Precondition Violation";

        return new ArrayDafnySequence<T>(Arrays.copyOfRange(seq, lo, hi));
    }

    @Override
    @SuppressWarnings("unchecked")
    protected List<T> asList() {
        return (List) Arrays.asList(seq);
    }

    @Override
    public DafnySequence<T> concatenate(DafnySequence<T> other) {
        if (other instanceof ArrayDafnySequence) {
            Object[] otherSeq = ((ArrayDafnySequence) other).seq;
            Object[] newArray = new Object[seq.length + otherSeq.length];
            System.arraycopy(seq, 0, newArray, 0, seq.length);
            System.arraycopy(otherSeq, 0, newArray, seq.length, otherSeq.length);
            return new ArrayDafnySequence<T>(newArray);
        } else {
            return super.concatenate(other);
        }
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
    public DafnySequence<Byte> concatenate(DafnySequence<Byte> other) {
        if (other instanceof ByteArrayDafnySequence) {
            byte[] otherArray = ((ByteArrayDafnySequence) other).array;
            byte[] newArray = new byte[array.length + otherArray.length];
            System.arraycopy(array, 0, newArray, 0, array.length);
            System.arraycopy(otherArray, 0, newArray, array.length, otherArray.length);
            return new ByteArrayDafnySequence(newArray);
        } else {
            return super.concatenate(other);
        }
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
    public DafnySequence<Character> concatenate(DafnySequence<Character> other) {
        if (other instanceof StringDafnySequence) {
            String otherString = ((StringDafnySequence) other).string;
            return new StringDafnySequence(string + otherString);
        } else {
            return super.concatenate(other);
        }
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
