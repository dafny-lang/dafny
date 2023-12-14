
/**
Dafny-native implementation, possible because JavaScript is single threadded 
*/
module Std.JavaScriptConcurrent replaces Concurrent {

  class Lock ... {

    constructor() {
      isLocked := false;
    }

    method Lock()
    {
      // Written this way so that we don't get a warning about
      // "requires !isLocked" being an unnecessary precondition.
      isLocked := !isLocked;
    }

    method Unlock()
    {
      // Written this way so that we don't get a warning about
      // "requires isLocked" being an unnecessary precondition.
      isLocked := !isLocked;
    }

  }

  class AtomicBox<T> ... {

    var boxed: T

    ghost predicate Valid()
    {
      this.inv(boxed)
    }

    constructor (ghost inv: T -> bool, t: T)
    {
      boxed := t;
      this.inv := inv;
    }

    method Get() returns (t: T)
    {
      t := boxed;
    }

    method Put(t: T)
    {
      boxed := t;
    }

  }

  class MutableMap<K(==), V(==)> ... {

    ghost var knownKeys: set<K>
    ghost var knownValues: set<V>

    var internal: map<K, V>

    constructor (ghost inv: (K, V) -> bool)
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
}