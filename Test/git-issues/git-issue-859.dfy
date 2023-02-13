// RUN: %testDafnyForEachCompiler "%s"

datatype FailureCompatible = Make {
  predicate IsFailure() { true }
  function PropagateFailure(): int { 12 }
  function Extract(): (r: real) { 0.0 }
}

method M() returns (r: FailureCompatible) { }

method N() returns (x: int) {
  var s: real :- M();
  return 13;
}

method Main() {
  var x := N();
  print x, "\n";
}

