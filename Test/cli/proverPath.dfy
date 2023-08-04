// RUN: %baredafny verify %args --solver-path="%z3" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
method m() {
  assert 1 + 1 == 2;
}
