package DafnyClasses;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class DafnyString extends DafnySequence<Character>{

    public DafnyString(List<Character> l){
        this.seq =  l.toArray(new Character[l.size()]);
    }

    public DafnyString concatenate(DafnyString otherSeq){
        List<Character> l = new ArrayList<>(Arrays.asList(seq));
        for(int i =0; i < otherSeq.length(); i++){
            l.add(otherSeq.seq[i]);
        }
        return new DafnyString(l);
    }

    public DafnyString update(int i, Character t){
        List<Character> l = new ArrayList<>(Arrays.asList(seq));
        l.set(i, t);
        return new DafnyString(l);
    }

    public DafnyString subsequence(int lo, int hi){
        List<Character> l = new ArrayList<>();
        for(int i = lo; i< hi; i++){
            l.add(seq[i]);
        }
        return new DafnyString(l);
    }

    public DafnyString drop(int lo){
        List<Character> l = new ArrayList<>();
        for(int i = lo; i< this.length(); i++){
            l.add(seq[i]);
        }
        return new DafnyString(l);
    }

    public DafnyString take(int hi){
        List<Character> l = new ArrayList<>();
        for(int i = 0; i< hi; i++){
            l.add(seq[i]);
        }
        return new DafnyString(l);
    }


    public DafnyMultiset<Character> asDafnyMultiset(){
        DafnyMultiset<Character> d = new DafnyMultiset<>(Arrays.asList(seq));
        return d;
    }

}
