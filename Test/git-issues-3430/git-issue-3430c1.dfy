// RUN: %exits-with 0 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module B
}

module B {
}
