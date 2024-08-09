// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

method M() {}

method B() {
  var i := 0;
  while i < 3 {
    M() by {
      break;
    }
    i := i + 1;
  }
}
