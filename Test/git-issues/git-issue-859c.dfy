// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype FailureCompatible = Make {
  ghost predicate IsFailure() { true }
  ghost function PropagateFailure(): real { 12.0 }
  ghost method Extract() returns (r: real) { }
}

datatype FailureCompatible2 = Make {
  predicate IsFailure() { true }
  function PropagateFailure(): real { 12.0 }
  ghost method Extract() returns (r: real) { }
}

datatype FailureCompatible3 = Make {
  predicate IsFailure() { true }
  function PropagateFailure(): real { 12.0 }
  method Extract() returns (r: real) { }
}

method M() returns (r: FailureCompatible) { }
method M2() returns (r: FailureCompatible2) { }
method M3() returns (r: FailureCompatible3) { }

method NN2() returns (ss: real) {
  var s4 :- M2(); // OK - s4 is auto-ghost, so is ghost to match Extract in FailureCompatible2
  var s5 :- M3(); // OK - not ghost
  print s4, s5; // ERROR - s4 is ghost
}

