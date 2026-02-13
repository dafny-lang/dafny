// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method AttemptAtBinding0(x: int) {
  assert (x := 1 decreases to x - 1); // parsing error
}

method AttemptAtBinding1(x: int) {
  assert (0 := x decreases to x - 1); // parsing error
}

method AttemptAtBinding2(x: int) {
  assert (000 := x nonincreases to x - 1); // parsing error
}

method AttemptAtBinding3(x: int) {
  assert (ghost y := x decreases to x - 1); // parsing error
}

method BadUseOfGhost0(x: int) {
  assert (ghost x decreases to x - 1); // parsing error
}

method BadUseOfGhost1(x: int) {
  assert (x + 1, ghost x nonincreases to x - 1); // parsing error
}
