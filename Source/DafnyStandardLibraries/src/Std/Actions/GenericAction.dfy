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
  // so the definition of a MostlyGenericAction
  // that may only modify the heap deterministically
  // is left as an invitation to the sufficiently motivated Dafny contributor!)
  //
  // The more specific Action trait can be much more pleasant to use
  // when composing non-interferring actions together,
  // such as working with enumerators or streams,
  // as they make simplifying assumptions that are true for many reusable actions.
  // However, this more general action may be more flexible
  // when accepting any kind of callback in a higher-order method.
  trait GenericAction<I, O> {

    // Specification predicates

    ghost predicate Requires(i: I)
      reads Reads(i)
    ghost function Reads(i: I): set<object>
      reads this
      ensures this in Reads(i)
    ghost function Modifies(i: I): set<object>
      reads Reads(i)
    ghost function Decreases(i: I): TerminationMetric
      reads Reads(i)
    twostate predicate Ensures(i: I, new o: O)
      requires old(Requires(i))
      reads Reads(i)

    // Actual action implementation

    method Invoke(i: I) returns (o: O)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      // TODO: Can the ", 0" part be rolled into the TerminationMetric instead?
      decreases Decreases(i).Ordinal(), 0
      ensures Ensures(i, o)
  }

}