package DafnyClasses;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Spliterator;
import java.util.function.Consumer;
import java.util.stream.Collectors;

public class DafnyString implements Iterable {
    //Todo: this should be re-written to use a Java string internally
    /*
    Invariant: forall 0<=i<length(). seq[i] != null
    Property: DafnyStrings are immutable. Any methods that seem to edit the DafnyString will only return a new
    DafnyString
     */

    private String inner;

    public DafnyString(){
        inner = "";
    }

    public DafnyString(List<Character> inList) {
        assert inList != null && !inList.contains(null) : "Precondition Violation";
        StringBuilder sb = new StringBuilder();
        for (Character c : inList) {
            sb.append(c);
        }
        inner = sb.toString();
    }

    // Uses property that Java Strings are immutable
    public DafnyString(DafnyString other) {
        assert other != null : "Precondition Violation";
        inner = other.inner;
    }

    // Uses property that Java Strings are immutable
    public DafnyString(String s) {
        assert s != null : "Precondition Violation";
        inner = s;
    }

    private DafnyString(String s, int i, Character c) {
        assert 0 <= i && c != null && s != null : "Precondition Violation";
        inner = s.substring(0, i) + c.toString() + s.substring(i + 1);
    }

    // Determines if this DafnyString is a prefix of other
    public boolean isPrefixOf(DafnyString other) {
        assert other != null : "Precondition Violation";
        if (other.length() < length()) return false;
        return other.inner.substring(0, length()).equals(inner);
    }

    // Determines if this DafnyString is a proper prefix of other
    public boolean isProperPrefixOf(DafnyString other) {
        assert other != null : "Precondition Violation";
        return length() < other.length() && isPrefixOf(other);
    }

    public DafnyString concatenate(DafnyString other) {
        assert other != null : "Precondition Violation";
        return new DafnyString(inner + other.inner);
    }

    public Character select(int i) {
        assert 0 <= i && i < length() : "Precondition Violation";
        return inner.charAt(i);
    }

    public int length() {
        return inner.length();
    }

    public DafnyString update(int i, char t) {
        assert 0 <= i && i < length() : "Precondition Violation";
        return new DafnyString(inner, i, t);
    }

    public boolean contains(char c) {
        return inner.contains(Character.toString(c));
    }

    // Returns the substring of values [lo..hi)
    public DafnyString subsequence(int lo, int hi) {
        assert 0 <= hi && 0 <= lo && lo <= hi : "Precondition Violation";
        return new DafnyString(inner.substring(lo, hi));
    }

    // Returns the substring of values [lo..length())
    public DafnyString drop(int lo) {
        assert lo >= 0 && lo < length() : "Precondition Violation";
        return new DafnyString(inner.substring(lo));
    }

    // Returns the substring of values [0..hi)
    public DafnyString take(int hi) {
        assert hi >= 0 && hi <= length() : "Precondition Violation";
        return new DafnyString(inner.substring(0, hi));
    }

    public DafnySequence<DafnyString> slice(List<Integer> inList) {
        assert inList != null : "Precondition Violation";
        List<DafnyString> list = new ArrayList<>();
        int curr = 0;
        for (Integer i : inList) {
            assert i != null : "Precondition Violation";
            list.add(subsequence(curr, curr + i));
            curr += i;
        }

        return new DafnySequence<>(list);
    }

    public DafnyMultiset<Character> asDafnyMultiset() {
        return new DafnyMultiset(toList());
    }

    @Override
    public String toString() {
        return inner;
    }


    @Override
    public void forEach(Consumer action) {
        assert action != null : "Precondition Violation";
        toList().forEach(action);
    }

    @Override
    public Iterator iterator() {
        return toList().iterator();
    }

    @Override
    public Spliterator spliterator() {
        return toList().spliterator();
    }

    @Override
    public int hashCode() {
        return inner.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnyString o = (DafnyString) obj;
        if (length() != o.length()) return false;
        return inner.equals(o.inner);
    }

    @Override
    protected Object clone() throws CloneNotSupportedException {
        return super.clone();
    }

    private List<Character> toList() {
        return inner.chars().mapToObj(e -> (char) e).collect(Collectors.toList());
    }
}
