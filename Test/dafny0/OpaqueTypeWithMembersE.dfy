// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type FailureCompatible(0) {
  const c: int
  compiled predicate IsFailure() { c < 10 }
  compiled function PropagateFailure(): int
    requires IsFailure()
  {
    100 / (c - 10)
  }
  compiled function Extract(): real
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
