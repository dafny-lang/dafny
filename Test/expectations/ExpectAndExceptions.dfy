// RUN: ! %dafny /compile:3 /compileTarget:cs /unicodeChar:0 "%s" > "%t"
// RUN: ! %dafny /compile:3 /compileTarget:go /unicodeChar:0 "%s" >> "%t"
// RUN: ! %dafny /compile:3 /compileTarget:java /unicodeChar:0 "%s" >> "%t"
// RUN: ! %dafny /compile:3 /compileTarget:js /unicodeChar:0 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/NatOutcomeDt.dfy"
include "../exceptions/GenericOutcomeDt.dfy"

method TestAssignOrHalt() {
    var stmt1: nat :- expect NatSuccess(42);
    // Regression test for when assign-or-halt was also calling PropagateFailure, which led
    // to the error "type variable 'U' in the function call to 'PropagateFailure' could not be determined"
    // (because of the lack of type constraints).
    var stmt2: string :- expect Success("Hooray!");

    var stmt3: nat :- expect NatFailure("Kaboom!");
}

method Main() {
  TestAssignOrHalt();
}