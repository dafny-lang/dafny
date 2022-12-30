// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Foo = Bar(x: int)

method letTest() {
  assert (var (Bar(a), c) := (Bar(1), 2); a) == 1;
}
