// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M {
  type TT = int
}

module MA {
  module Inner {
    type T17 = x | 0 <= x < 17
  }
}

module MB {
  module I {
    type T42 = x | 0 <= x < 42
    type T43 = x | 0 <= x < 43
  }
}

module B {
  import MAI = MA.Inner // now OK
  import MA.Inner // now OK
}

module C {
  import MB
  import II = MB.K // error - no K
  import MB.K // error - no K
}
