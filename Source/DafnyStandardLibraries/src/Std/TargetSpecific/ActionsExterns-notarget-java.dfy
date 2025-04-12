/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:extern} Std.JavaActionsExterns replaces ActionsExterns {

  method {:extern} {:axiom} MakeSetReader<T>(s: set<T>) returns (p: Producer<T>, ghost proof: ProducerOfSetProof<T>)
}