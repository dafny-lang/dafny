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

method N() returns (s: real) {
  ghost var ss: real := 1.0;
  s :- M(); // ERRORS - IsFailure, PropagateFailure are ghost; Extract is ghost assigning to non-ghost
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
  var s1 :- M(); // ERRORS - IsFailure, PropagateFailure; s1 is auto-ghost so OK to get non-ghost value from Extract
  print s1, "\n"; // verifying s1 is non-ghost
}

