// RUN: %verify "%s" > "%t"
// RUN: %verify --solver-option='PROVER_PATH=%z3' "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
method m() {
  assert 1 + 1 == 2;
}
