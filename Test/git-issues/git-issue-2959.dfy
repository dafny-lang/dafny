// RUN: %exits-with 4 %baredafny build --use-basename-for-filename --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method NondetIf() returns (x: int) {
  if * {
    x := 0;
  } else {
    x := 1;
  }
}

method AlsoNondetIf() returns (x: int) {
  var b: bool;
  if b {
    x := 0;
  } else {
    x := 1;
  }
}

method NondetAssign() returns (x: int) {
  x := *;
}

method AlsoNondetAssignButAccepted() returns (x: int) {
  var y: int;
  x := y;
}

method ArrayAllocation() returns (x: int) {
  var a := new int[10];
  return a[0];
}
