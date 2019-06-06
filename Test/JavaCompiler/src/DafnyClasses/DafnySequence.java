package DafnyClasses;

import java.util.*;
import java.util.function.Consumer;

public class DafnySequence<T> implements Iterable{
    protected T[] seq;

    public DafnySequence(){

    }

    public DafnySequence(List<T> l){
        this.seq = (T[]) l.toArray();
    }

    public boolean prefix(DafnySequence<T> otherSeq){
        if(otherSeq.length() > this.length())
            return false;
        for(int i = 0; i < otherSeq.length(); i++){
            if(seq[i] != otherSeq.select(i))
                return false;
        }

        return true;
    }

    public boolean properPrefix(DafnySequence<T> otherSeq){
        return this.length() > otherSeq.length() && this.prefix(otherSeq);
    }

    public DafnySequence<T> concatenate(DafnySequence<T> otherSeq){
        List<T> l = new ArrayList<T>(Arrays.asList(seq));
        for(int i =0; i < otherSeq.length(); i++){
            l.add(otherSeq.seq[i]);
        }
        return new DafnySequence<>(l);
    }

    public T select(int i){
        return seq[i];
    }

    public int length(){
        return seq.length;
    }

    public DafnySequence<T> update(int i, T t){
        List<T> l = new ArrayList<T>(Arrays.asList(seq));
        l.set(i, t);
        return new DafnySequence<>(l);
    }

    public boolean contains(T t){
        return Arrays.asList(seq).contains(t);
    }

    public DafnySequence<T> subsequence(int lo, int hi){
        List<T> l = new ArrayList<>();
        for(int i = lo; i< hi; i++){
            l.add(seq[i]);
        }
        return new DafnySequence<>(l);
    }

    public DafnySequence<T> drop(int lo){
        List<T> l = new ArrayList<>();
        for(int i = lo; i< this.length(); i++){
            l.add(seq[i]);
        }
        return new DafnySequence<>(l);
    }

    public DafnySequence<T> take(int hi){
        List<T> l = new ArrayList<>();
        for(int i = 0; i< hi; i++){
            l.add(seq[i]);
        }
        return new DafnySequence<>(l);
    }

    public DafnySequence<DafnySequence<T>> slice(List<Integer> l){
        List<DafnySequence<T>> list = new ArrayList<>();
        int curr = 0;
        for(Integer i : l){
            List<T> innerList = new ArrayList<>();
            for(int j = 0; j < i; j++){
                innerList.add(seq[curr+j]);
            }
            curr += i;
            list.add(new DafnySequence<>(innerList));
        }

        return new DafnySequence<>(list);
    }

    public DafnyMultiset<T> asDafnyMultiset(){
        DafnyMultiset<T> d = new DafnyMultiset<>(Arrays.asList(seq));
        return d;
    }

    @Override
    public void forEach(Consumer action) {
        Arrays.asList(seq).forEach(action);
    }

    @Override
    public Spliterator spliterator() {
        return Arrays.asList(seq).spliterator();
    }

    @Override
    public Iterator iterator() {
        return Arrays.asList(seq).iterator();
    }

    @Override
    public boolean equals(Object obj) {
        // self check
        if (this == obj)
            return true;
        // null check
        if (obj == null)
            return false;
        // type check and cast
        if (getClass() != obj.getClass())
            return false;
        DafnySequence<T> o = (DafnySequence<T>) obj;
        // field comparison
        if(this.length() != o.length())
            return false;
        for(int i = 0; i < this.length(); i++){
            if(seq[i] != o.select(i))
                return false;
        }
        return true;
    }
}
