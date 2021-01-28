// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Error - circular

module D {
  import E
}

module E {
  import D
}
