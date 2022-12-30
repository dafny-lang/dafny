// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file is just a small test to check that constructors do cause loops

datatype Nat = Zero | Succ(x: Nat)
function f(n: Nat): Nat

method M() {
  assert forall s :: true || f(Succ(s)) == f(s);
}
