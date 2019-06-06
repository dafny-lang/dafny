package DafnyClasses;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.Predicate;
import java.util.stream.Stream;

public class DafnySet<T> implements Iterable, Collection, Set {
    Set<T> innerHash;
    public DafnySet(){
        this.innerHash = new HashSet();
    }

    public DafnySet(Set<T> s){
        this.innerHash = (HashSet) s;
    }


    public boolean isSubset(DafnySet<T> otherSet){
        return this.containsAll(otherSet);
    }

    public boolean isProperSubset(DafnySet<T> otherSet){
        return this.isSubset(otherSet) && (this.size() > otherSet.size());
    }


    public boolean contains(Object o){
        return this.innerHash.contains(o);
    }

    public boolean disjoint(DafnySet<T> otherSet){
        for (T ele: this.innerHash
             ) {
            if(otherSet.contains(ele))
                return false;
        }
        return true;
    }

    public DafnySet<T> union(DafnySet<T> otherSet){
        DafnySet<T> u = new DafnySet<>();
        u.addAll(otherSet);
        u.addAll(this);
        return u;
    }

    public DafnySet<T> difference(DafnySet<T> otherSet){
        DafnySet<T> u = new DafnySet<>();
        u.addAll(this);
        u.removeAll(otherSet);
        return u;
    }

    public DafnySet<T> intersection(DafnySet<T> otherSet){
        DafnySet<T> u = new DafnySet<>();
        for (T ele: this.innerHash
             ) {
            if (otherSet.contains(ele))
                u.add(ele);
        }
        return u;
    }

    @Override
    public boolean containsAll(Collection c) {
        return this.innerHash.containsAll(c);
    }

    @Override
    public int size() {
        return this.innerHash.size();
    }

    @Override
    public Iterator iterator() {
        return this.innerHash.iterator();
    }

    @Override
    public boolean isEmpty() {
        return this.innerHash.isEmpty();
    }

    @Override
    public Object[] toArray() {
        return this.innerHash.toArray();
    }

    @Override
    public T[] toArray(Object[] a) {
        return (T[]) this.innerHash.toArray(a);
    }

    @Override
    public boolean add(Object o) {
        return this.innerHash.add((T) o);
    }

    @Override
    public boolean remove(Object o) {
        return this.innerHash.remove((T) o);
    }

    @Override
    public boolean removeAll(Collection c) {
        return this.innerHash.removeAll(c);
    }

    @Override
    public boolean addAll(Collection c) {
        return this.innerHash.addAll(c);
    }

    @Override
    public boolean retainAll(Collection c) {
        return this.innerHash.retainAll(c);
    }

    @Override
    public boolean removeIf(Predicate filter) {
        return this.innerHash.removeIf(filter);
    }

    @Override
    public T[] toArray(IntFunction generator) {
        return (T[]) this.innerHash.toArray(generator);
    }

    @Override
    public Spliterator spliterator() {
        return this.innerHash.spliterator();
    }

    @Override
    public Stream parallelStream() {
        return this.innerHash.parallelStream();
    }

    @Override
    public Stream stream() {
        return this.innerHash.stream();
    }

    @Override
    public void clear() {
        this.innerHash.clear();
    }

    @Override
    public void forEach(Consumer action) {
        this.innerHash.forEach(action);
    }

    @Override
    protected Object clone() throws CloneNotSupportedException {
        return super.clone();
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
        DafnySet<T> o = (DafnySet<T>) obj;
        // field comparison
        return this.containsAll(o) && o.containsAll(this);
    }

    @Override
    public int hashCode() {
        return this.innerHash.hashCode();
    }

    @Override
    public String toString() {
        return this.innerHash.toString();
    }
}
