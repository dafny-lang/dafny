/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.GenericActions {

  import opened Termination

  // A trait to express any imperative action in Dafny.
  // This is essentially a reflective interface for a method,
  // with all possible specifications attached.
  // It can also be thought of as the logical last step
  // in the progression of arrow types,
  // from the total, heap-independent ->,
  // to the partial but still heap-independent -->,
  // to the heap-reading ~>.
  // A generic action is thus like a function that can also modify the heap.
  //
  // (The behavior of a generic action may also be non-deterministic,
  // but this case seems less useful in practice,
  // so the definition of a MostlyGenericFunction
  // that may only modify the heap deterministically
  // is left as an invitation to the sufficiently motivated Dafny contributor!)
  //
  // The more specific Action trait can be much more pleasant to use
  // when composing non-interferring actions together,
  // such as working with enumerators or streams,
  // as they make simplifying assumptions that are true for many reusable actions.
  // However, this more general action may be more flexible
  // when accepting any kind of callback in a higher-order method.
  trait GenericAction<T, R> {

    // Specification predicates

    ghost predicate Requires(t: T)
      reads Reads(t)
    ghost function Reads(t: T): set<object>
      reads this
      ensures this in Reads(t)
    ghost function Modifies(t: T): set<object>
      reads Reads(t)
    ghost function Decreases(t: T): TerminationMetric
      reads Reads(t)
    twostate predicate Ensures(t: T, new r: R)
      reads Reads(t)

    // Actual action implementation

    method Invoke(t: T) returns (r: R)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
  }

}