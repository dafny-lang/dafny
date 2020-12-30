// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %dafny /compile:0 /z3exe:"%z3" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
method m() {
  assert 1 + 1 == 2;
}
