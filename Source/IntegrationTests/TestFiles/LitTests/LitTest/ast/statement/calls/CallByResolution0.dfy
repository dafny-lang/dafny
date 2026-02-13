// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

method M() {}

method A() {
  var i: int := 0;
  M() by {
    i := 1;
    return;
  }
}
