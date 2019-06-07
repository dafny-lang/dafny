package DafnyClasses;

import java.util.ArrayList;
import java.util.List;

public class DafnyString extends DafnySequence<Character> {
    //Todo: this should be re-written to use a Java string internally
    /*
    Invariant: forall 0<=i<length(). seq[i] = null || Character
    Property: DafnyStrings are immutable. Any methods that seem to edit the DafnyString will only return a new
    DafnyString
     */
    public DafnyString(List<Character> l){
        assert  l != null && !l.contains(null): "Precondition Violation";
        seq =  new ArrayList<>(l);
    }

    public DafnyString(DafnyString other) {
        assert  other != null : "Precondition Violation";
        seq = new ArrayList<>(other.seq);
    }

    public DafnyString concatenate(DafnyString other){
        assert  other != null : "Precondition Violation";
        List<Character> l = new ArrayList<>(seq);
        l.addAll(other.seq);
        return new DafnyString(l);
    }

    public DafnyString update(int i, Character t){
        assert  i >= 0 && i < length() && t != null : "Precondition Violation";
        List<Character> l = new ArrayList<>(seq);
        l.set(i, t);
        return new DafnyString(l);
    }

    // Returns the substring of values [lo..hi)
    public DafnyString subsequence(int lo, int hi){
        assert  lo >= 0 && hi >= 0 && hi >= lo : "Precondition Violation";
        return new DafnyString(seq.subList(lo, hi));
    }

    // Returns the substring of values [lo..length())
    public DafnyString drop(int lo){
        assert  lo >= 0 && lo < length() : "Precondition Violation";
        return new DafnyString(seq.subList(lo, length()));
    }

    // Returns the substring of values [0..hi)
    public DafnyString take(int hi){
        assert  hi >= 0 && hi <= length() : "Precondition Violation";
        return new DafnyString(seq.subList(0, hi));
    }

    public DafnyMultiset<Character> asDafnyMultiset(){
        DafnyMultiset<Character> d = new DafnyMultiset<>(seq);
        return d;
    }

    public String toString(){
        StringBuilder sb = new StringBuilder();
        for(Character c : seq){
            sb.append(c);
        }
        return sb.toString();
    }
}
