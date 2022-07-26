module A {
  module B {
    const S1 := 10
  }
}

const S2 := 21

module C {
  module D {
    import A // OK
    import A.B // OK
    import E // OK
    import E.F // OK
    // import C // NOT OK
    const X := B.S1 // OK
    // const Y := S2 // NOT OK
  }
  module E {
    module F {
    }
  }
}

