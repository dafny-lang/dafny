// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module
  least predicate m[nat]() {}
}

module B {
  module least
  predicate m[nat]() {}
}
