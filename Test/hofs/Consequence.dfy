// RUN: %baredafny verify %args --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Nat = x | 0 <= x

method Check() {
  var f : Nat -> Nat;
  assume f.requires(0);
  var i : Nat := f(0);
}
