// RUN: %exits-with 4 %verify --solver-path=doesNotExist "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Fatal Error: ProverException: Cannot find specified prover:.*
method m() {
  assert 1 + 1 == 2;
}
