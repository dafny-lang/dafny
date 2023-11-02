// RUN: %testDafnyForEachResolver "%s"


method Test1(a: array<(int, int)>, b: array<(int, int, ghost int)>) {
  assert a as object != b;
}

method Test2(a: array<(int, int)>, b: array<(int, ghost int)>) {
  assert a as object != b;
}
