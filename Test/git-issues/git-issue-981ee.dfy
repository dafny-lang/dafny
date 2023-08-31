// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module B {
  module E2 {}
  import E2 = Z // error
}
