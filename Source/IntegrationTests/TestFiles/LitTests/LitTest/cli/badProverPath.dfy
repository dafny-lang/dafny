// RUN: %exits-with 4 %verify --solver-path=doesNotExist "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Z3 not found. Please either provide a path to the `z3` executable using
method m() {
  assert 1 + 1 == 2;
}
