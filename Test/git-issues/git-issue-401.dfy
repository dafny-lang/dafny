// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /compile:0 /proverOpt:PROVER_PATH="%z3" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: windows
method m() {
  assert 1 + 1 == 2;
}
