// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Error - circular

module D {
  import E
}

module E {
  import D
}
