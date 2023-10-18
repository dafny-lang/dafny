// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype X = X
lemma Foo(x: X) returns (y: bool) {
  match x {
    case X => return old(x) == x;
    case _ =>
  }
  return false;
}
