// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "./NatOutcome.dfy"
include "./VoidOutcome.dfy"

method MultiAssignmentNotAllowed(r1: NatOutcome, r2: NatOutcome) returns (res: NatOutcome) {
    var a0, b0 := r1, r2; // <-- multi-assignment allowed
    var a0, b0 :- r1, r2; // <-- multi-assignment not allowed
    return a0;
}

method MultiRHSNotAllowed(r1: VoidOutcome, r2: VoidOutcome) returns (res: VoidOutcome) {
    :- r1;      // one RHS is ok
    :- r1, r2;  // more than one RHS is not ok
    return r1;
}
