// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module K {
  module KK {
    module KKK {
      const k := 10
    }
  }
}

// Checks that refines does resolve a qualified ID
// and does not use a local module
module L refines K.KK.KKK {
  module K {}
  method m() { assert k == 10; }
}
module L1 refines K.KK.KKK {
  import K = AAA`E
  method m() { assert k == 10; }
}
module L2 refines K.KK.KKK {
  import opened AAA`E
  method m() { assert k == 10; }
}

// Checks for name conflicts/redeclarations during
// refining
module AAA {
  export E reveals *
  export F reveals *
  module K{}
  module M{}
}

module BBB refines AAA {
  export E provides * // error: duplicate declaration
  export F ... provides * // OK: refining declaration
  module M{} // error: duplicate declaration
}


module AA {}
module CC {
  import AA`AA  // error: No explicit export set AA
}
module BB refines AA {
  export BB extends AA // error: No explicit export set AA
}

// Testing some exports and extension errors
module A {
  export reveals a
  export C reveals a
  const a := 10
  const D := 20
}

module B refines A {
  export reveals *
  export Q extends C
  export R extends K // Error: no export set K
  export S extends D // Error: no export set D
}


module C refines A {
  // OK
  const b := 30
}

module C' {
  import Z = C     // same as C`C
  import Y = C`C
  method m() {
    assert Z.b == 30; // error
    assert Y.a == 10;
    assert Z.a == 30;
    assert Y.b == 20; // error
  }
}

module D refines A {
  // OK. D in A is not an export set
}

module E {
  export E reveals *
  const F := 40
  method F() {} // error: reuse of name F
  const E := 30 // OK: export sets are in a different namespace
}

