// RUN: %exits-with 4 %verify --solver-path=doesNotExist "%s" > "%t"
// RUN: %exits-with 4 %build --solver-path=doesNotExist "%s" >> "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Z3 not found at 
// CHECK: Z3 not found at 
method m() {
  assert 1 + 1 == 2;
}
