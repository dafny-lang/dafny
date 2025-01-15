// RUN: ! %run --target cs "%s" > "%t"
// RUN: ! %run --target go "%s" >> "%t"
// RUN: ! %run --target java "%s" >> "%t"
// RUN: ! %run --target js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "../exceptions/NatOutcomeDt.dfy"
include "../exceptions/GenericOutcomeDt.dfy"

method TestAssignOrHalt() {
    var stmt1: nat :- expect NatSuccess(42) by {
       assert true;
    }
    // Regression test for when assign-or-halt was also calling PropagateFailure, which led
    // to the error "type variable 'U' in the function call to 'PropagateFailure' could not be determined"
    // (because of the lack of type constraints).
    var stmt2: string :- expect Success("Hooray!");

    var stmt3: nat :- expect NatFailure("Kaboom!");
}

method Main() {
  TestAssignOrHalt();
}