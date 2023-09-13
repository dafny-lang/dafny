// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
// RUN: %diff "%s.expect" "%t"

module A {  // error: cyclic import
  import B
  module X { }
}
module B {
  import A.X
}

