// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


// When a function call violates two preconditions at the same time, it causes
// two errors to be reported for the same token

method A(x: int)
  requires x > 0
  requires x < 0
{}

method B(x: int) {
  A(x);
}

ghost function fA(x: int): int
  requires x > 0
  requires x < 0 { 1 }

ghost function fB(x: int): int { fA(x) }
