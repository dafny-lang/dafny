// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype FailureCompatible = Make {
  predicate IsFailure() { true }
  function PropagateFailure(): real { 12.0 }
  ghost method Extract() returns (r: real) { }
}

datatype FailureCompatible2 = Make {
  predicate method IsFailure() { true }
  function method PropagateFailure(): real { 12.0 }
  ghost method Extract() returns (r: real) { }
}

datatype FailureCompatible3 = Make {
  predicate method IsFailure() { true }
  function method PropagateFailure(): real { 12.0 }
  method Extract() returns (r: real) { }
}

method M() returns (r: FailureCompatible) { }
method M2() returns (r: FailureCompatible2) { }
method M3() returns (r: FailureCompatible3) { }

method N() returns (s: real) {
  ghost var ss: real := 1.0;
  s :- M(); // ERRORS
}

method N1() returns (s: real) {
  ghost var ss: real := 1.0;
  s :- M2(); // ERROR - ghost assigned to non-ghost
}

method N2() returns (s: real) {
  ghost var ss: real := 1.0;
  s :- M3(); // OK
  ss :- M2(); // OK
  ss :- M3(); // OK
}

method NN() returns (ss: real) {
  var s1 :- M(); // ERRORS
}

method NN2() returns (ss: real) {
  var s4 :- M2(); // OK - s4 is auto-ghost
  var s5 :- M3(); // OK
  print s4, s5; // ERROR - s4 is ghost
}

method Main() {
  var x := N();
  print x, "\n";
}

