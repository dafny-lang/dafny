
module {:compile false} Std.JavaScriptConcurrent replaces Concurrent {

  class {:extern} MutableMap<K(==), V(==)> ... {

    constructor {:extern} {:axiom} (ghost inv: (K, V) -> bool)

    ghost predicate Valid()
    {
      true
    }

    method {:extern} {:axiom} Keys() returns (keys: set<K>)

    method {:extern} {:axiom} HasKey(k: K) returns (used: bool)

    method {:extern} {:axiom} Values() returns (values: set<V>)

    method {:extern} {:axiom} Items() returns (items: set<(K,V)>)

    method {:extern} {:axiom} Put(k: K, v: V)

    method {:extern} {:axiom} Get(k: K) returns (r: Option<V>)

    method {:extern} {:axiom} Remove(k: K)

    method {:extern} {:axiom} Size() returns (c: nat)

  }

  class {:extern} AtomicBox<T> ... {

    constructor {:extern} {:axiom} (ghost inv: T -> bool, t: T)

    ghost predicate Valid() { true }

    method {:extern} {:axiom} Get() returns (t: T)

    method {:extern} {:axiom} Put(t: T)

  }

  class {:extern} Lock ... {

    constructor {:extern} {:axiom} ()

    method {:extern} {:axiom} Lock()

    method {:extern} {:axiom} Unlock()

  }
}

// Dafny-native implementation, used to generate the extern implementation
module {:extern "Std_Concurrent"} Std.ConcurrentDafny {

  import opened Wrappers

  class MutableMap<K(==), V(==)> {

    ghost const inv: (K, V) -> bool
    ghost var knownKeys: set<K>
    ghost var knownValues: set<V>

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
      reads this
    {
      forall k :: k in internal.Keys ==> inv(k, internal[k]) && Contained()
    }

    method Keys() returns (keys: set<K>)
      requires Valid()
      ensures forall k :: k in keys ==> exists v :: v in knownValues && inv(k,v)
    {
      reveal Contained();
      keys := internal.Keys;
    }

    method HasKey(k: K) returns (used: bool)
      requires Valid()
      ensures used ==> exists v :: v in knownValues && inv(k,v)
    {
      reveal Contained();
      used := k in internal.Keys;
    }

    method Values() returns (values: set<V>)
      requires Valid()
      ensures forall v :: v in values ==> exists k :: k in knownKeys && inv(k,v)
    {
      reveal Contained();
      values := internal.Values;
    }

    method Items() returns (items: set<(K,V)>)
      requires Valid()
      ensures forall t :: t in items ==> inv(t.0, t.1)
    {
      items := internal.Items;
    }

    method Get(k: K) returns (r: Option<V>)
      requires Valid()
      ensures r.Some? ==> inv(k, r.value)
    {
      r := if k in internal.Keys then Some(internal[k]) else None;
    }

    method Put(k: K, v: V)
      requires Valid()
      requires inv(k, v)
      modifies this
      ensures Valid()

    {
      internal := internal[k := v];
      knownKeys := knownKeys + {k};
      knownValues := knownValues + {v};
      reveal Contained();
    }

    method Remove(k: K)
      requires Valid()
      requires exists v :: inv(k,v)
      modifies this
      ensures Valid()
    {
      // only here to mollify the auditor
      assert exists v :: inv(k,v);

      internal := internal - {k};
      reveal Contained();
    }

    method Size() returns (c: nat)
      requires Valid()
    {
      // only here to mollify the auditor
      reveal Contained();
      assert Contained();

      c := |internal|;
    }

  }

  class AtomicBox<T> {

    ghost const inv: T -> bool

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
      reads this
    {
      inv(boxed)
    }

    method Get() returns (t: T)
      requires Valid()
      ensures inv(t)
    {
      t := boxed;
    }

    method Put(t: T)
      requires inv(t)
      modifies this
      ensures Valid()
    {
      boxed := t;
    }

  }

  class Lock {

    ghost var isLocked: bool

    constructor() {
      isLocked := false;
    }

    method Lock()
      requires !isLocked
      modifies this
      ensures isLocked
    {
      // Written this way so that we don't get a warning about
      // "requires !isLocked" being an unnecessary precondition.
      isLocked := !isLocked;
    }

    method Unlock()
      requires isLocked
      modifies this
      ensures !isLocked
    {
      // Written this way so that we don't get a warning about
      // "requires isLocked" being an unnecessary precondition.
      isLocked := !isLocked;
    }

  }

}
