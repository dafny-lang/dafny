// RUN: %testDafnyForEachResolver "%s"


datatype Foo = Bar(x: int)

method letTest() {
  assert (var (Bar(a), c) := (Bar(1), 2); a) == 1;
}
