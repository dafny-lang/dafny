// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


method test() returns (a: bool, b: int) {
  return (true, 0);
}
