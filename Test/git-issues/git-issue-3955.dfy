// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  var x: int
  predicate Valid() reads this {
    x >= 0
  }
}

datatype B = B(
  a: A
) {
  opaque predicate Valid()
    reads a
  {
    a.Valid()
  }
}

class C {
  var a: A
  constructor()
  opaque twostate predicate Valid()
    reads this`a, a
  {
    a.Valid() && old(a.Valid())
  }
}