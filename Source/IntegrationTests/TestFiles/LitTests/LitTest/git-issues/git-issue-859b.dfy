// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype FailureCompatible = Make {
  ghost predicate IsFailure() { true }
  ghost function PropagateFailure(): real { 12.0 }
  ghost method Extract() returns (r: real) { }
}

datatype FailureCompatible2 = Make {
  predicate IsFailure() { true }
  function PropagateFailure(): real { 12.0 }
  ghost function Extract(): real { 9.0 }
}

datatype FailureCompatible3 = Make {
  predicate IsFailure() { true }
  function PropagateFailure(): real { 12.0 }
  function Extract(): real { 9.0 }
}

method M() returns (r: FailureCompatible) { }
method M2() returns (r: FailureCompatible2) { }
method M3() returns (r: FailureCompatible3) { }

method N() returns (s: real) {
  ghost var ss: real := 1.0;
  var sss := ss; // auto ghost now works for initializations from expressions
  print ss, sss; // ERROR - ghost expressions
}

method NN() returns (ss: real) {
  var s4 :- M2(); // OK - s4 is auto-ghost
  var s5 :- M3(); // OK
  print s4, s4+1.0, s5; // ERROR - two ghost expressions
}

