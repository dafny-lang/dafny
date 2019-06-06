package DafnyClasses;

import java.math.BigInteger;
import java.util.*;

public class DafnyMultiset<T> {
    private Map<T, BigInteger> innerHash;
    public DafnyMultiset(){
        this.innerHash = new HashMap<>();
    }

    public DafnyMultiset(Map<T, BigInteger> m){
        this.innerHash = new HashMap<>(m);
    }

    public DafnyMultiset(Set<T> s){


        DafnyMultiset<T> d = new DafnyMultiset<>();
        for (T t: s
             ) {
            //todo see if this still works without the if statement
            if(d.contains(t))
                d.update(t, new BigInteger("1").add(d.multiplicity(t)));
            else
                d.update(t, new BigInteger("1"));
        }
    }

    public DafnyMultiset(List<T> l){


        this.innerHash = new HashMap<>();
        for (T t: l
        ) {
            //todo see if this still works without the if statement
            if(innerHash.containsKey(t))
                innerHash.put(t, new BigInteger("1").add(innerHash.get(t)));
            else
                innerHash.put(t, new BigInteger("1"));
        }
    }

    public BigInteger cardinality(){
        BigInteger b = new BigInteger("0");
        for (BigInteger big: this.innerHash.values()
             ) {
            b = b.add(big);
        }
        return b;
    }

    public boolean isSubset(DafnyMultiset<T> otherMulti){
        for (Map.Entry<T, BigInteger> entry: otherMulti.getInnerHash().entrySet()
             ) {
            if(!this.innerHash.containsKey(entry.getKey()) || this.innerHash.get(entry.getKey()).compareTo(entry.getValue()) < 0)
                return false;
        }
        return true;
    }

    public boolean isProperSubset(DafnyMultiset<T> otherMulti){
        return this.isSubset(otherMulti) && this.cardinality().compareTo(otherMulti.cardinality()) > 0;
    }

    public boolean contains(T t){
        return this.innerHash.containsKey(t);
    }

    public boolean disjoint(DafnyMultiset<T> otherMulti){
        for (T t: otherMulti.getInnerHash().keySet()
        ) {
            if(this.innerHash.containsKey(t))
                return false;
        }
        return true;
    }

    public BigInteger multiplicity(T t){
        return this.innerHash.get(t);
    }

    public void update(T t, BigInteger b){
        if(b.compareTo(new BigInteger("0")) == 0){
            this.innerHash.remove(t);
            return;
        }
        this.innerHash.put(t, b);
    }

    public DafnyMultiset<T> union(DafnyMultiset<T> otherMulti){
        DafnyMultiset<T> u = new DafnyMultiset<>();
        for (Map.Entry<T, BigInteger> entry: this.innerHash.entrySet()
             ) {
            u.update(entry.getKey(), entry.getValue());
        }
        for (Map.Entry<T, BigInteger> entry: otherMulti.innerHash.entrySet()
        ) {
            if(u.contains(entry.getKey()))
                u.update(entry.getKey(), u.multiplicity(entry.getKey()).add(entry.getValue()));
            else
                u.update(entry.getKey(), entry.getValue());
        }
        return u;
    }

    public DafnyMultiset<T> difference(DafnyMultiset<T> otherMulti){
        DafnyMultiset<T> u = new DafnyMultiset<>();
        for (Map.Entry<T, BigInteger> entry: this.innerHash.entrySet()
        ) {
            if(!otherMulti.contains(entry.getKey()))
                u.update(entry.getKey(), entry.getValue());
            else if(entry.getValue().compareTo(otherMulti.multiplicity(entry.getKey()))> 0)
                u.update(entry.getKey(), entry.getValue().subtract(otherMulti.multiplicity(entry.getKey())));
        }

        return u;
    }

    public DafnyMultiset<T> intersection(DafnyMultiset<T> otherMulti){
        DafnyMultiset<T> u = new DafnyMultiset<>();
        for (Map.Entry<T, BigInteger> entry: this.innerHash.entrySet()
        ) {
            if(otherMulti.contains(entry.getKey()))
                u.update(entry.getKey(), entry.getValue().min(otherMulti.multiplicity(entry.getKey())));
        }

        return u;
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
        DafnyMultiset<T> o = (DafnyMultiset<T>) obj;
        // field comparison
        return this.innerHash.equals(o.getInnerHash());
    }

    @Override
    public int hashCode() {
        return this.innerHash.hashCode();
    }

    @Override
    public String toString() {
        return this.innerHash.toString();
    }

    public Map<T, BigInteger> getInnerHash() {
        return innerHash;
    }
}
