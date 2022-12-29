// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "./NatOutcome.dfy"
include "./VoidOutcome.dfy"

method MultiAssignment(r1: NatOutcome, r2: NatOutcome) returns (res: NatOutcome) {
    var a0, b0 := r1, r2; // <-- multi-assignment allowed
    var a1, b1 :- r1, r2; // <-- multi-assignment allowed
    var a2, b2 :- r2; // <-- mismatch in number
    var a3, b3 :- 100, 101; // <-- mismatch in type
    return a0;
}

method MultiRHS(r1: VoidOutcome, r2: nat) returns (res: VoidOutcome) {
    :- r1;      // one RHS is ok
    :- r1, r2;  // more than one RHS is not ok, without a LHS
    var t1 :- r1, r2; // OK
    var t2: nat :- r1, r2; // OK
    return r1;
}
