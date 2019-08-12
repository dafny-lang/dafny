// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "./NatOutcome.dfy"

method MultiAssignmentNotAllowed(r1: NatOutcome, r2: NatOutcome) returns (res: NatOutcome) {
    var a0, b0 := r1, r2; // <-- multi-assignment allowed
    var a0, b0 :- r1, r2; // <-- multi-assignment not allowed
    return a0;
}
