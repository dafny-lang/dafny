// Dafny should emit exit value 1
// RUN: ! %dafny /compile:0 /proverOpt:PROVER_PATH=Output/binz/z3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  assert 1 + 1 == 2;
}
