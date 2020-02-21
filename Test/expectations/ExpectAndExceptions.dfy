// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/NatOutcome.dfy"

method TestAssignOrHalt() {
    var stmt1: nat :- expect MakeNatSuccess(42);
    var stmt2: nat :- expect MakeNatFailure("Kaboom!");
}

method Main() {
  TestAssignOrHalt();
}