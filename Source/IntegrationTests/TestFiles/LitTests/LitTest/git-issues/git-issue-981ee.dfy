// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module B {
  module E2 {}
  import E2 = Z // error
}
