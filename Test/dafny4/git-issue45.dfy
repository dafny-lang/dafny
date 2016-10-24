// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Library {
}

module Outer {
  import Library

  module Inner {
    import Library
  }
}
