replaceable module Std.Concurrent {

  import opened Wrappers

  /**
    * A lock to provide mutual exclusion.
    *
    * Note this lock is not reentrant, and its methods have preconditions
    * to ensure they are called in matching pairs.
    */
  class Lock {

    // This is really "thread-local" state.
    // {:concurrent} will not allow the use of Locks because of it,
    // but that's a good thing because Locks by themselves cannot make
    // verification sound under concurrent execution.
    ghost var isLocked: bool

    constructor()
      ensures !isLocked

    /**
      * Acquires the lock.
      */
    method Lock()
      requires !isLocked
      reads this
      modifies this
      ensures isLocked

    /**
      * Releases the lock.
      */
    method Unlock()
      requires isLocked
      reads this
      modifies this
      ensures !isLocked
  }

  /**
    * A mutable wrapper for a single value that is safe to access
    * by multiple concurrent executions.
    */
  class AtomicBox<T> {

    // Invariant on values this box may hold
    ghost const inv: T -> bool

    constructor (ghost inv: T -> bool, t: T)
      requires inv(t)
      ensures this.inv == inv

    method Get() returns (t: T)
      reads {}
      ensures inv(t)

    method Put(t: T)
      reads {}
      requires inv(t)
  }

  /**
    * A mutable wrapper for a map that is safe to access
    * by multiple concurrent executions.
    * 
    * Functionally equivalent to an AtomicBox<map<K, V>>
    * but will be much more efficient in practice.
    */
  class MutableMap<K(==), V(==)> {

    // Invariant on key-value pairs this map may hold
    ghost const inv: (K, V) -> bool

    // The bytesKeys parameter allows for more efficient implementations.
    // Currently only has any effect in Go, to enable O(1) lookup instead of O(n).
    // This MUST NOT be set to true if K is not seq<uint8>,
    // otherwise the behavior of this map is undefined.
    constructor (ghost inv: (K, V) -> bool, bytesKeys: bool := false)
      ensures this.inv == inv

    method Keys() returns (keys: set<K>)
      reads {}
      ensures forall k <- keys :: exists v :: inv(k, v)

    method HasKey(k: K) returns (used: bool)
      reads {}
      ensures used ==> exists v :: inv(k, v)

    method Values() returns (values: set<V>)
      reads {}
      ensures forall v <- values :: exists k :: inv(k,v)

    method Items() returns (items: set<(K,V)>)
      reads {}
      ensures forall t <- items :: inv(t.0, t.1)

    method Put(k: K, v: V)
      reads {}
      requires inv(k, v)

    method Get(k: K) returns (r: Option<V>)
      reads {}
      ensures r.Some? ==> inv(k, r.value)

    method Remove(k: K)
      reads {}
      // TODO: this isn't really necessary, if it's not true
      // then Remove(k) will just never have any effect
      requires exists v :: inv(k, v)

    method Size() returns (c: nat)
      reads {}
  }
}