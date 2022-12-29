// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  export
    provides
      Opened,
      f

  module Opened {
    type T = int
  }

  function f(x: Opened.T): int {
    5
  }
}
