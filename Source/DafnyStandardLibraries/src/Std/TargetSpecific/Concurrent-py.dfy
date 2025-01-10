@Compile(false)
module Std.PythonConcurrent replaces Concurrent {

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