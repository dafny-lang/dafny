// RUN: %baredafny verify %args --solver-log="log.smt2" --resource-limit 10 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "log.smt2" "%s"
// CHECK: rlimit 10000
method m() {
  assert 1 + 1 == 2;
}
