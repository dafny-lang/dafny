// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module Z {}
module A {
  export E1 reveals *
  export E2 reveals *
  export E3 reveals *
  export E4 reveals *
  export E5 reveals *
  export E6 reveals *
  module E1 {}
  import E2 = Z
  type T3
  const E4 := 0
  method E5() {}
  class E6 {}
}
module AA {
  export E reveals *
  export E reveals * // error
}

