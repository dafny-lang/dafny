// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module X { }
}
module B {
  import A.X  // used to require an 'import A' first
}

