// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "./NatOutcome.dfy"

method Test() returns (res: NatOutcome) {
    var a0 := MakeNatSuccess("not a nat");
    var a  :- MakeNatSuccess("not a nat either");
    return a0;
}

method RedeclareVar() returns (res: NatOutcome) {
    var a := MakeNatSuccess(42);
    var a :- MakeNatSuccess(43);
    var b :- MakeNatSuccess(44);
    var b := MakeNatSuccess(45);
    return a;
}
