// RUN: %dafny /compile:0 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
  }
}

module A {

  import TTT = M

  import M

  import MA
  import MAI = MA.Inner
  import MA.Inner
  import MB
  import II = MB.I

  class ZZ {
    var zc: II.T42
    var zd: M.TT
    var ze: TTT.TT
    var zf: MAI.T17
    var zg: Inner.T17
    var zh: MA.Inner.T17
  }
}
