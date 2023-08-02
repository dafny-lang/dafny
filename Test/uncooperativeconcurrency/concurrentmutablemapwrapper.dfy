

class SequentialMutableMap<K, V> {

    ghost var Repr: set<object>
    ghost var value: map<K, V>

    constructor()
        ensures value == map[]
    {
        value := map[];
    }

    method Put(k: K, v: V)
        modifies Repr
        ensures value == old(value)[k := v]
        ensures fresh(Repr - old(Repr))

    // etc...
}

class ConcurrencyMutableMapWrapper<K(!new), V(!new)> {

    const wrapped: SequentialMutableMap<K, V>

    ghost const inv: (K, V) -> bool
    ghost var {:separatedHeap} Repr: set<object>
    
    constructor(ghost inv: (K, V) -> bool) 
        ensures Valid()
    {
        wrapped := new SequentialMutableMap();
        this.inv := inv;
        new;
        Repr := {this} + {wrapped} + wrapped.Repr;
    }

    ghost predicate Valid() 
        reads this, Repr
    {
        && this in Repr
        && wrapped in Repr
        && wrapped.Repr <= Repr
        // Required for a separate class, since it will lock <this>
        // for every function and method.
        // && forall o <- Repr :: o.owner == this
        && forall k, v | (k, v) in wrapped.value.Items :: inv(k, v)
    }

    method Put(k: K, v: V)
        requires Valid()
        requires inv(k, v)
        modifies this, Repr
        ensures Valid()
    {
        wrapped.Put(k, v);

        Repr := {this} + {wrapped} + wrapped.Repr;
        forall o <- wrapped.Repr - old(wrapped.Repr) {
            assert fresh(o);

            // Should be legal since o is fresh?
            // o.owner := this;
        }
    }

    // Similarly for other methods...
}