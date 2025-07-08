// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


method NonGhost(x: int) {
  expect x - 1 decreases to x; // error: cannot use ghost expression here
}

method GhostVariable(x: int) returns (c: bool) {
  ghost var b := x - 1 decreases to x; // b is inferred to be ghost
  c := b; // error: cannot assign ghost to non-ghost
}

/* TODO: this currently crashes the resovler
method InferredGhost(x: int) returns (c: bool) {
  var b := x - 1 decreases to x; // b is inferred to be ghost
  c := b; // error: cannot assign ghost to non-ghost
}
*/
