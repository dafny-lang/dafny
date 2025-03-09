/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.GenericActions {

  import opened Termination

  //
  // A fully general action.
  //
  // See https://github.com/dafny-lang/dafny/blob/master/Source/DafnyStandardLibraries/src/Std/Actions/Actions.md
  // for further details.
  //
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