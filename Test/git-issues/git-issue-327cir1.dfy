// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


module A {
  module B {
    module C {
    }
  }

  import B
}

