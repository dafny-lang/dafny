// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// Error - circular

module D {
  module E {
    import D
  }
}
