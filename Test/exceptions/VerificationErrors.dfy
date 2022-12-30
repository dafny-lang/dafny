// RUN: %exits-with 4 %baredafny verify %args "%s" --rprint="%t.rprint" > "%t"
// RUN: %diff "%s.expect" "%t"

include "./NatOutcome.dfy"
include "./VoidOutcome.dfy"

method CheckThatVerifierRunsInsideDesugaredExprs_Nat(r1: NatOutcome, r2: NatOutcome) returns (res: NatOutcome) {
    var a :- MakeNatSuccess(assert r1 == r2; 12);
    res := MakeNatSuccess(a);
}

method CheckThatVerifierRunsInsideDesugaredExprs_Void(r1: VoidOutcome, r2: VoidOutcome) returns (res: VoidOutcome) {
    var x := assert 2 + 2 == 4; 8;
    assert x == 8;
    :- (assert r1 == r2; r1);
    res := r1;
}
