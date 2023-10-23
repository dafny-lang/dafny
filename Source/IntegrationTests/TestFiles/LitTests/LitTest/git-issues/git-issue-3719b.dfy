// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

opaque predicate P(i: int) { true }

method testCallOpaqueAssert() {
  assert f0: P(0) by {
    reveal P();
  }
  assert P(0) by {
    reveal f0;
  }
}