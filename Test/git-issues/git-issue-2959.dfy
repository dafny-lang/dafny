// RUN: %exits-with 4 %baredafny build --use-basename-for-filename --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method NondetIf() returns (x: int) {
  if * {
    x := 0;
  } else {
    x := 1;
  }
}

method NondetAssign() returns (x: int) {
  x := *;
}
