// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype FailureCompatible = Make {
  predicate IsFailure() { true }
  function PropagateFailure(): real { 12.0 }
  ghost method Extract() returns (r: real) { }
}

method M() returns (r: FailureCompatible) { }

method N() returns (s: real) {
  s :- M(); // ERRORS
}

method Main() {
  var x := N();
  print x, "\n";
}

