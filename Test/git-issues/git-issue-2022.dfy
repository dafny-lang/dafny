// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  export
    provides
      Opened,
      f

  module Opened {
    type T = int
  }

  ghost function f(x: Opened.T): int {
    5
  }
}
