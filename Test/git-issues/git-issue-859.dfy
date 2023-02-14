// RUN: %testDafnyForEachCompiler "%s"

datatype FailureCompatible = Make {
  predicate method IsFailure() { true }
  function method PropagateFailure(): int { 12 }
  function method Extract(): real { 9.0 }
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

