// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
//
method M3(x: int) {
  assert (x := 1 decreases to x - 1);
}
