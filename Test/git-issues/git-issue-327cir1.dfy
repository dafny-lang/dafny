// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
// RUN: %diff "%s.expect" "%t"


module A {
  module B {
    module C {
    }
  }

  import B
}

