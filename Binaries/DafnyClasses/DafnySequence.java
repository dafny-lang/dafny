package DafnyClasses;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class DafnySequence<T> implements Iterable {
    /*
    Invariant: forall 0<=i<length(). seq[i] == T || null
    Property: DafnySequences are immutable. Any methods that seem to edit the DafnySequence will only return a new
    DafnySequence
    Todo: DafnySequence Invariants and Properties
     */
    protected ArrayList<T> seq;

    public DafnySequence() {
    }

    public static DafnySequence<Character> asString(String s){
        return new DafnySequence<>(s.chars()
                .mapToObj(e -> (char)e)
                .collect(Collectors.toList()));
    }

    private DafnySequence(List<T> l, int i, T t){
        seq = new ArrayList<>(l);
        seq.set(i, t);
    }

    public DafnySequence(List<T> l) {
        assert l != null: "Precondition Violation";
        seq = new ArrayList<>(l);
    }

    public DafnySequence(DafnySequence<T> other) {
        assert other != null : "Precondition Violation";
        seq = new ArrayList<>(other.seq);
    }

    // Determines if this DafnySequence is a prefix of other
    public boolean isPrefixOf(DafnySequence<T> other) {
        assert other != null : "Precondition Violation";
        if (other.length() < length()) return false;
        for (int i = 0; i < length(); i++) {
            if (seq.get(i) != other.select(i)) return false;
        }

        return true;
    }

    // Determines if this DafnySequence is a proper prefix of other
    public boolean isProperPrefixOf(DafnySequence<T> other) {
        assert other != null : "Precondition Violation";
        return length() < other.length() && isPrefixOf(other);
    }

    public DafnySequence<T> concatenate(DafnySequence<T> other) {
        assert other != null : "Precondition Violation";
        List<T> l = new ArrayList(seq);
        l.addAll(other.seq);
        return new DafnySequence<>(l);
    }

    public T select(int i) {
        assert i >= 0 : "Precondition Violation";
        return seq.get(i);
    }

    public int length() {
        return seq.size();
    }

    public DafnySequence<T> update(int i, T t) {
        //todo: should we allow i=length, and return a new sequence with t appended to the sequence?
        assert 0 <= i && i < length(): "Precondition Violation";
        return new DafnySequence<>(seq, i, t);
    }

    public DafnySequence<T> update(BigInteger b, T t) {
        //todo: should we allow i=length, and return a new sequence with t appended to the sequence?
        assert b.compareTo(BigInteger.ZERO) >=0  &&
                b.compareTo(new BigInteger(Integer.toString(length()))) < 0: "Precondition Violation";
        return new DafnySequence<>(seq, b.intValue(), t);
    }

    public boolean contains(T t) {
        assert t != null : "Precondition Violation";
        return seq.contains(t);
    }

    // Returns the subsequence of values [lo..hi)
    public DafnySequence<T> subsequence(int lo, int hi) {
        assert lo >= 0 && hi >= 0 && hi >= lo : "Precondition Violation";
        return new DafnySequence<>(seq.subList(lo, hi));
    }


    // Returns the subsequence of values [lo..length())
    public DafnySequence<T> drop(int lo) {
        assert lo >= 0 && lo < length() : "Precondition Violation";
        return new DafnySequence<>(seq.subList(lo, length()));
    }


    // Returns the subsequence of values [0..hi)
    public DafnySequence<T> take(int hi) {
        assert hi >= 0 && hi <= length() : "Precondition Violation";
        return new DafnySequence<>(seq.subList(0, hi));
    }

    public DafnySequence<DafnySequence<T>> slice(List<Integer> l) {
        assert l != null : "Precondition Violation";
        List<DafnySequence<T>> list = new ArrayList<>();
        int curr = 0;
        for (Integer i : l) {
            assert i != null : "Precondition Violation";
            list.add(new DafnySequence<>(subsequence(curr, curr + i)));
            curr += i;
        }

        return new DafnySequence<>(list);
    }

    public DafnyMultiset<T> asDafnyMultiset() {
        return new DafnyMultiset<>(seq);
    }

    @Override
    public void forEach(Consumer action) {
        assert action != null : "Precondition Violation";
        seq.forEach(action);
    }

    @Override
    public Spliterator spliterator() {
        return seq.spliterator();
    }

    @Override
    public Iterator iterator() {
        return seq.iterator();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnySequence<T> o = (DafnySequence<T>) obj;
        if (length() != o.length()) return false;
        return seq.equals(o.seq);
    }

    @Override
    public int hashCode() {
        return seq.hashCode();
    }

    @Override
    public String toString() {
        return seq.toString();
    }

    public String verbatimString(){
        StringBuilder builder = new StringBuilder(seq.size());
        for(Character ch: (ArrayList<Character>) seq)
        {
            builder.append(ch);
        }
        return builder.toString();
    }
}
