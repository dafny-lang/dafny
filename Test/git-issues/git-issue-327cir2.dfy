// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
// RUN: %diff "%s.expect" "%t"

// Error - circular

module D {
  import E
}

module E {
  import D
}
