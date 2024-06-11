// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// Error - circular

module D {
  import E
}

module E {
  import D
}
