// RUN: %testDafnyForEachResolver "%s"


module A {
  module X { }
}
module B {
  import A.X  // used to require an 'import A' first
}

