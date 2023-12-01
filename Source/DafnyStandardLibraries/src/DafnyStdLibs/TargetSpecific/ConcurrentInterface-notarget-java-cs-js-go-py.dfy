abstract module DafnyStdLibs.ConcurrentInterface {

  import opened Wrappers

  /**
    * A reentrant lock to provide mutual exclusion.
    */
  class Lock {

    /**
     * Acquires the lock.
     *
     * If this concurrent execution already holds the lock,
     * increments the hold count for this execution.
     * If not, blocks until the lock is no longer held.
     */
    method Lock()

    /**
     * Releases the lock.
     *
     * If this concurrent execution currently holds the lock,
     * decrements the hold count for this execution.
     * If this count becomes zero, releases the lock.
     *
     * Has no effect if the lock was not currently held by this concurrent execution.
     */
    method Unlock()
  }

  /**
    * A mutable wrapper for a single value that is safe to access
    * by multiple concurrent executions.
    */
  class AtomicBox<T> {

    // Invariant on values this box may hold
    ghost const inv: T -> bool

    ghost predicate Valid()
      reads this

    method Get() returns (t: T)
      requires Valid()
      ensures inv(t)

    method Put(t: T)
      requires inv(t)
      modifies this
      ensures Valid()
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
    ghost var knownKeys: set<K>
    ghost var knownValues: set<V>

    ghost predicate Valid()
      reads this

    method Keys() returns (keys: set<K>)
      requires Valid()
      ensures forall k :: k in keys ==> exists v :: v in knownValues && inv(k,v)

    method HasKey(k: K) returns (used: bool)
      requires Valid()
      ensures used ==> exists v :: v in knownValues && inv(k,v)

    method Values() returns (values: set<V>)
      requires Valid()
      ensures forall v :: v in values ==> exists k :: k in knownKeys && inv(k,v)

    method Items() returns (items: set<(K,V)>)
      requires Valid()
      ensures forall t :: t in items ==> inv(t.0, t.1)

    method Put(k: K, v: V)
      requires Valid()
      requires inv(k, v)
      modifies this
      ensures Valid()

    method Get(k: K) returns (r: Option<V>)
      requires Valid()
      ensures r.Some? ==> inv(k, r.value)

    method Remove(k: K)
      requires Valid()
      requires exists v :: inv(k,v)
      modifies this
      ensures Valid()

    method Size() returns (c: nat)
      requires Valid()
  }
}