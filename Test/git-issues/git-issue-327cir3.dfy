// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {  // error: cyclic import
  import B
  module X { }
}
module B {
  import A.X
}

