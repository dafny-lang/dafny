// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(): int {
  var p := x => true;
  assert true by {
    forall y: int | p(y) {}
  }
  5
}
