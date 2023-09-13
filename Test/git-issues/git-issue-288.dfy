// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
// RUN: %diff "%s.expect" "%t"

module A {
  type T = int
}

module B refines A {
  type T = int
}
