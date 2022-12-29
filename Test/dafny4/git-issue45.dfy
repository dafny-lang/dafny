// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Library {
}

module Outer {
  import Library

  module Inner {
    import Library
  }
}
