// RUN: %exits-with 4 %baredafny verify %args --verbosity Trace --solver-opt BATCH_MODE=true "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Running in batch mode.
method m(x: int) {
  if x == 1 {
    assert x != 1;
  } else if x == 2 {
    assert x != 2;
  } else if x == 3 {
    assert x != 3;
  }
}
