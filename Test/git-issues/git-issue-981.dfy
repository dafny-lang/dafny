// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
/*
module K {
  module KK {
    module KKK {
      const k := 10;
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
*/
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

// OK to extend the default export set
module AA {}
module BB refines AA {
  export BB extends AA
}

// Testing some exports and extension errors
module A {
  export reveals a
  export C reveals a
  const a := 10;
  const D := 20;
}

module B refines A {
  export reveals *
  export Q extends C
  export R extends K // Error
  export S extends D // Error
}


module C refines A {
  // error: forbidden refinement because A has a non-default C
}

module D refines A {
  // OK. D in A is not an export set
}

module E {
  export E reveals *
  const F := 40;
  method F() {} // error: reuse of name F
  const E := 30; // export sets in different namespace
}

