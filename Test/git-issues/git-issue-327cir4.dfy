// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Error - circular

module D {
  module E {
    import D
  }
}
