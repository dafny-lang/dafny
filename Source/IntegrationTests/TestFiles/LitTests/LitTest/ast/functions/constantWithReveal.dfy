// RUN: %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

opaque function Foo(x: int): int {
  x
}

const C := reveal Foo(); Foo(42)