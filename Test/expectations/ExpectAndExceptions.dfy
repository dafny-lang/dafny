// RUN: %dafny /compile:3 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /compileTarget:go "%s" >> "%t"
// TODO-RS: Need to fix the inconsistent handling of verbatimString() in Java
// RUN: %dafny /compile:3 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/NatOutcomeDT.dfy"

method TestAssignOrHalt() {
    var stmt1: nat :- expect NatSuccess(42);
    var stmt2: nat :- expect NatFailure("Kaboom!");
}

method Main() {
  TestAssignOrHalt();
}