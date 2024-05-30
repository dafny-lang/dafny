// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
//
method NonGhost(x: int) {
  expect (x - 1 decreases to x);
}
