module DafnyStdLibs.Concurrent refines ConcurrentInterface {

 class MutableMap<K(==), V(==)> ... {

    var internal: map<K, V>

    constructor (inv: (K, V) -> bool)
      ensures Valid()
      ensures this.inv == inv
    {
      internal := map[];
      this.inv := inv;
      this.knownKeys := {};
      this.knownValues := {};
    }

    opaque ghost predicate Contained()
      reads this`internal, this`knownKeys, this`knownValues
    {
      internal.Keys <= knownKeys && internal.Values <= knownValues
    }

    ghost predicate Valid()
    {
      forall k :: k in internal.Keys ==> inv(k, internal[k]) && Contained()
    }

    method Keys() returns (keys: set<K>)
    {
      reveal Contained();
      keys := internal.Keys;
    }

    method HasKey(k: K) returns (used: bool)
    {
      reveal Contained();
      used := k in internal.Keys;
    }

    method Values() returns (values: set<V>)
    {
      reveal Contained(); 
      values := internal.Values;
    }

    method Items() returns (items: set<(K,V)>)
    {
      items := internal.Items;
    }

    method Get(k: K) returns (r: Option<V>)
    {
      r := if k in internal.Keys then Some(internal[k]) else None;
    }

    method Put(k: K, v: V)
    {
      internal := internal[k := v];
      knownKeys := knownKeys + {k};
      knownValues := knownValues + {v};
      reveal Contained();
    }

    method Remove(k: K)
    {
      // only here to mollify the auditor
      assert exists v :: inv(k,v);

      internal := internal - {k};
      reveal Contained();
    }

    method Size() returns (c: nat)
    {
      // only here to mollify the auditor
      reveal Contained();
      assert Contained();
    
      c := |internal|;
    }

  }

  class AtomicBox<T> ... {
    var boxed: T

    constructor (inv: T -> bool, t: T)
      requires inv(t)
      ensures Valid()
      ensures this.inv == inv
    {
      boxed := t;
      this.inv := inv;
    }

    ghost predicate Valid()
    {
      inv(boxed)
    }

    method Get() returns (t: T)
      ensures inv(t)
    {
      t := boxed;
    }

    method Put(t: T)
      ensures Valid()
    {
      boxed := t;
    }

  }

  class Lock ... {

    constructor() {}

    method Lock() {}

    method Unlock() {}

  }

}