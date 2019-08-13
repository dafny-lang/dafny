// RUN: %dafny "%s" /dprint:"%t.dprint" > "%t"
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
    var a :- o; return o; // TODO infers '?' for RHS of ':-' instead of 'BadOutcome1'
}

method TestMissingMethods2(o: BadOutcome2) returns (res: BadOutcome2) {
    var a :- o; return o; // TODO infers 'BadOutcome2?' for RHS of ':-' instead of 'BadOutcome2' (should not infer nullable)
}

method TestMissingMethods3(o: BadOutcome3) returns (res: BadOutcome3) {
    var a :- o; return o; // TODO infers 'BadOutcome3?' for RHS of ':-' instead of 'BadOutcome3' (should not infer nullable)
}
