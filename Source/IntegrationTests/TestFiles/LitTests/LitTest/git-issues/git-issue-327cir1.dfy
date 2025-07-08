// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"



module A {
  module B {
    module C {
    }
  }

  import B
}

