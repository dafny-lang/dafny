// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type FailureCompatible(0) {
  const c: int
  predicate method IsFailure() { c < 10 }
  function method PropagateFailure(): int
    requires IsFailure()
  {
    100 / (c - 10)
  }
  function method Extract(): real
    requires !IsFailure()
  {
    100.0 / c as real
  }
}

method M() returns (r: FailureCompatible) {
  r :| true;
}

method N() returns (x: int) {
  var s :- M();
  var t: real := s;
}
