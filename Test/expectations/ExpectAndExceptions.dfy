// RUN: %dafny /compile:3 /compileTarget:go "%s" > "%t"
// RUN: %dafny /compile:3 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/NatOutcomeDT.dfy"

method TestAssignOrHalt() {
    var stmt1: nat :- expect NatSuccess(42);
    var stmt2: nat :- expect NatFailure("Kaboom!");
}

method Main() {
  TestAssignOrHalt();
}