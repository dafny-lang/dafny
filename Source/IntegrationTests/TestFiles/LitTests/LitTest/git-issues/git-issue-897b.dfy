// RUN: %testDafnyForEachResolver "%s"


ghost function F(): int {
  var p := x => true;
  assert true by {
    forall y: int | p(y) {}
  }
  5
}
