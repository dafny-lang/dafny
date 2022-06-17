// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Error - circular

module D {
  module E {
    import D
  }
}
