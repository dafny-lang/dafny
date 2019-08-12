// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "./NatOutcome.dfy"

method CheckThatVerifierRunsInsideDesugaredExprs(r1: NatOutcome, r2: NatOutcome) returns (res: NatOutcome) {
    var a :- MakeNatSuccess(assert r1 == r2; 12);
    res := MakeNatSuccess(a);
}
