package DafnyClasses;

import java.util.Set;
import java.util.HashSet;

public class DafnySet<T> {
    private Set<T> innerSet;
    public DafnySet(){
        this.innerSet = new HashSet();
    }

    public DafnySet(Set<T> s){
        this.innerSet = (HashSet) s;
    }


    public boolean isSubset(DafnySet<T> otherSet){
        return this.containsAll(otherSet);
    }

    public boolean isProperSubset(DafnySet<T> otherSet){
        return this.isSubset(otherSet) && (this.size() > otherSet.size());
    }


    public boolean contains(Object o){
        return this.innerSet.contains(o);
    }

    public boolean disjoint(DafnySet<T> otherSet){
        for (T ele: this.innerSet
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
        for (T ele: this.innerSet
             ) {
            if (otherSet.contains(ele))
                u.add(ele);
        }
        return u;
    }

    public boolean containsAll(DafnySet c) {
        return this.innerSet.containsAll(c.innerSet);
    }

    public int size() {
        return this.innerSet.size();
    }



    public boolean isEmpty() {
        return this.innerSet.isEmpty();
    }


    public boolean add(Object o) {
        return this.innerSet.add((T) o);
    }

    public boolean remove(Object o) {
        return this.innerSet.remove((T) o);
    }

    public boolean removeAll(DafnySet c) {
        return this.innerSet.removeAll(c.innerSet);
    }

    public boolean addAll(DafnySet c) {
        return this.innerSet.addAll(c.innerSet);
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
        return this.innerSet.hashCode();
    }

    @Override
    public String toString() {
        return this.innerSet.toString();
    }

    public Set<T> getInnerSet(){
        return this.innerSet;
    }
}
