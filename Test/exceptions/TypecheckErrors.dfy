// RUN: %exits-with 2 %baredafny verify %args "%s" /dprint:"%t.dprint" > "%t"
// RUN: %diff "%s.expect" "%t"
include "./NatOutcome.dfy"
include "./VoidOutcome.dfy"

method TestTypecheckingInDesugaredTerm_Nat() returns (res: NatOutcome) {
    var a0 := MakeNatSuccess("not a nat");
    var a  :- MakeNatSuccess("not a nat either");
    return a0;
}

method RedeclareVar_Nat() returns (res: NatOutcome) {
    var a := MakeNatSuccess(42);
    var a :- MakeNatSuccess(43);
    var b :- MakeNatSuccess(44);
    var b := MakeNatSuccess(45);
    return a;
}

trait BadOutcome1 {
    // predicate method IsFailure() // <-- deliberately commented out
    // function method PropagateFailure(): BadOutcome1 requires IsFailure() // <-- deliberately commented out
    // function method Extract(): nat requires !IsFailure() // <-- deliberately commented out
}

trait BadOutcome2 {
    predicate method IsFailure()
    // function method PropagateFailure(): BadOutcome2 requires IsFailure() // <-- deliberately commented out
    function method Extract(): nat requires !IsFailure()
}

trait BadOutcome3 {
    predicate method IsFailure()
    function method PropagateFailure(): BadOutcome3 requires IsFailure()
    // function method Extract(): nat requires !IsFailure() // <-- deliberately commented out
}

method TestMissingMethods1(o: BadOutcome1) returns (res: BadOutcome1) {
    var a :- o; return o; // TODO infers 'BadOutcome1?' for RHS of ':-' instead of 'BadOutcome1' (should not infer nullable)
}

method TestMissingMethods2(o: BadOutcome2) returns (res: BadOutcome2) {
    var a :- o; return o; // TODO infers 'BadOutcome2?' for RHS of ':-' instead of 'BadOutcome2' (should not infer nullable)
}

method TestMissingMethods3(o: BadOutcome3) returns (res: BadOutcome3) {
    var a :- o; return o; // TODO infers 'BadOutcome3?' for RHS of ':-' instead of 'BadOutcome3' (should not infer nullable)
}

method TestTypecheckingInDesugaredTerm_Void() returns (res: VoidOutcome) {
    :- MakeVoidFailure(|"not a string because we take its length"|);
}

trait BadVoidOutcome1 {
    // predicate method IsFailure() // <-- deliberately commented out
    // function method PropagateFailure(): BadVoidOutcome1 requires IsFailure() // <-- deliberately commented out
}

trait BadVoidOutcome2 {
    predicate method IsFailure()
    // function method PropagateFailure(): BadVoidOutcome2 requires IsFailure() // <-- deliberately commented out
}

trait BadVoidOutcome3 {
    predicate method IsFailure()
    function method PropagateFailure(): BadVoidOutcome3 requires IsFailure()
    function method Extract(): nat requires !IsFailure() // <-- deliberately added, even though Void error handling must not have it
}

method TestMissingVoidMethods1(o: BadVoidOutcome1) returns (res: BadVoidOutcome1) {
    :- o; return o;
}

method TestMissingVoidMethods2(o: BadVoidOutcome2) returns (res: BadVoidOutcome2) {
    :- o; return o;
}

method TestMissingVoidMethods3(o: BadVoidOutcome3) returns (res: BadVoidOutcome3) {
    :- o; return o;
}
