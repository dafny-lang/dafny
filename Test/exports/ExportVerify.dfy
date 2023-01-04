// RUN: %exits-with 4 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Lib {
  export ProvideTypes
    provides *
  export MostlyProvides
    provides Ten, Two, Method
    provides D, D.M, D.P
    provides D.PI, D.n
  export Reveals
    reveals Ten, Two
    provides Method
    provides D, D.M, D.P
    reveals D.PI, D.n

  const Ten := 10

  function method Two(): int
    ensures Two() < 10
  { 2 }

  method Method() { }

  class D {
    static const PI := 3.14
    var u: int
    const n: int := 59
    constructor FromInt(x: int) { }
    method M() { }
    static method P() { }
  }
}

module Client_ProvideTypes {
  import Lib`ProvideTypes

  method M0() {
    var d: Lib.D;
    var u := d.n;  // error: to use d, it must first be initialized
  }
  method M1() {
    var d: Lib.D;
    d.M();  // error: to use d, it must first be initialized
  }
}

module Client_Providing {
  import Lib`MostlyProvides

  method M(d: Lib.D) {
    assert Lib.Ten == 10;  // error: RHS not known in this scope
    assert Lib.Two() < 10;
    assert Lib.Two() == 2;  // error: body not known in this scope
    assert Lib.D.PI == 3.14;  // error: RHS not known in this scope
    assert d.n == 59;  // error: RHS not known in this scope
    d.M();
    Lib.Method();
    Lib.D.P();
  }
}

module Client_Revealing {
  import Lib`Reveals

  method M(d: Lib.D) {
    assert Lib.Ten == 10;
    assert Lib.Two() < 10;
    assert Lib.Two() == 2;
    assert Lib.D.PI == 3.14;
    assert d.n == 59;
    d.M();
    Lib.Method();
    Lib.D.P();
    assert false;  // error
  }
}
