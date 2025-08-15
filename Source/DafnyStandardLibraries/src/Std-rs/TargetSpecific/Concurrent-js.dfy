@Compile(false)
module Std.JavaScriptConcurrent replaces Concurrent {

  class {:extern} MutableMap<K(==), V(==)> ... {

    @Axiom
    constructor {:extern} (ghost inv: (K, V) -> bool, bytesKeys: bool)

    ghost predicate Valid()
    {
      true
    }

    @Axiom
    method {:extern} Keys() returns (keys: set<K>)

    @Axiom
    method {:extern} HasKey(k: K) returns (used: bool)

    @Axiom
    method {:extern} Values() returns (values: set<V>)

    @Axiom
    method {:extern} Items() returns (items: set<(K,V)>)

    @Axiom
    method {:extern} Put(k: K, v: V)

    @Axiom
    method {:extern} Get(k: K) returns (r: Option<V>)

    @Axiom
    method {:extern} Remove(k: K)

    @Axiom
    method {:extern} Size() returns (c: nat)

  }

  class {:extern} AtomicBox<T> ... {

    @Axiom
    constructor {:extern} (ghost inv: T -> bool, t: T)

    ghost predicate Valid() { true }

    @Axiom
    method {:extern} Get() returns (t: T)

    @Axiom
    method {:extern} Put(t: T)

  }

  class {:extern} Lock ... {

    @Axiom
    constructor {:extern} ()

    @Axiom
    method {:extern} Lock()

    @Axiom
    method {:extern} Unlock()

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

    ghost predicate Contained()
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
      keys := internal.Keys;
    }

    method HasKey(k: K) returns (used: bool)
      requires Valid()
      ensures used ==> exists v :: v in knownValues && inv(k,v)
    {
      used := k in internal.Keys;
    }

    method Values() returns (values: set<V>)
      requires Valid()
      ensures forall v :: v in values ==> exists k :: k in knownKeys && inv(k,v)
    {
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
    }

    method Size() returns (c: nat)
    {
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
