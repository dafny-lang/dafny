// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

include "./NatOutcome.dfy"
include "./VoidOutcome.dfy"

method TestTypecheckingInDesugaredTerm_Nat() returns (res: NatOutcome) {
    var a0 := MakeNatSuccess("not a nat");
    var a  :- MakeNatSuccess("not a nat either");
    return a0;
}

method RedeclareVar_Nat() returns (res: NatOutcome) {
    var x := MakeNatSuccess(42);
    var a :- MakeNatSuccess(43);
    var b :- MakeNatSuccess(44);
    var y := MakeNatSuccess(45);
    return x;
}

trait BadOutcome1 {
    // predicate IsFailure() // <-- deliberately commented out
    // function PropagateFailure(): BadOutcome1 requires IsFailure() // <-- deliberately commented out
    // function Extract(): nat requires !IsFailure() // <-- deliberately commented out
}

trait BadOutcome2 {
    predicate IsFailure()
    // function PropagateFailure(): BadOutcome2 requires IsFailure() // <-- deliberately commented out
    function Extract(): nat requires !IsFailure()
}

trait BadOutcome3 {
    predicate IsFailure()
    function PropagateFailure(): BadOutcome3 requires IsFailure()
    // function Extract(): nat requires !IsFailure() // <-- deliberately commented out
}

method TestMissingMethods1(o: BadOutcome1) returns (res: BadOutcome1) {
    var a :- o; return o;
}

method TestMissingMethods2(o: BadOutcome2) returns (res: BadOutcome2) {
    var a :- o; return o;
}

method TestMissingMethods3(o: BadOutcome3) returns (res: BadOutcome3) {
    var a :- o; return o;
}

method TestTypecheckingInDesugaredTerm_Void() returns (res: VoidOutcome) {
    :- MakeVoidFailure(|"not a string because we take its length"|);
}

trait BadVoidOutcome1 {
    // predicate IsFailure() // <-- deliberately commented out
    // function PropagateFailure(): BadVoidOutcome1 requires IsFailure() // <-- deliberately commented out
}

trait BadVoidOutcome2 {
    predicate IsFailure()
    // function PropagateFailure(): BadVoidOutcome2 requires IsFailure() // <-- deliberately commented out
}

trait BadVoidOutcome3 {
    predicate IsFailure()
    function PropagateFailure(): BadVoidOutcome3 requires IsFailure()
    function Extract(): nat requires !IsFailure() // <-- deliberately added, even though Void error handling must not have it
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

method TestMissingMethods2WithKeyword(o: BadOutcome2) returns (res: BadOutcome2) {
  var a :- assert o; // with "assert" keyword, it's fine that PropagateFailure is missing
  return o;
}

method TestMissingVoidMethods2WithKeyword(o: BadVoidOutcome2) returns (res: BadVoidOutcome2) {
  :- assert o; // with "assert" keyword, it's fine that PropagateFailure is missing
  return o;
}
