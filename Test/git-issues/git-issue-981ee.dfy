// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module B {
  module E2 {}
  import E2 = Z // error
}
