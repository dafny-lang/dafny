/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.JavaCsActionsExterns replaces ActionsExterns {

  method MakeSetReader<T>(s: set<T>) returns (p: Producer<T>, ghost proof: ProducerOfSetProof<T>)
    ensures p.Valid()
    ensures fresh(p.Repr)
    ensures p.history == []
    ensures proof.Producer() == p
    ensures proof.Set() == s
  {
    expect false, "MakeSetReader is not implemented for this backend";
  }
}