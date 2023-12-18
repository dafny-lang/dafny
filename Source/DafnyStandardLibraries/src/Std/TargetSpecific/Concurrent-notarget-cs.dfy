module {:extern} {:compile false} Std.CSharpConcurrent replaces Concurrent {

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