// RUN: ! %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type T

datatype X = X(t: T)

method m(x1: X, x2: X) {
  var y := x1 == x2; // == can only be applied to expressions of types that support equality (got X)
}
