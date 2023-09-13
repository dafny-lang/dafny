// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
// RUN: %diff "%s.expect" "%t"

module B {
  module E2 {}
  import E2 = Z // error
}
