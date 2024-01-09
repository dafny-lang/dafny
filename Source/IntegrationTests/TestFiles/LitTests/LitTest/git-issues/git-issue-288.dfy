// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module A {
  type T = int
}

module B refines A {
  type T = int
}
