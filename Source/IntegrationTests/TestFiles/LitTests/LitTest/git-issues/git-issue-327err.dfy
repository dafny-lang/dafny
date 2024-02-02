// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module A {
  module AA {
    module AAA {
    }
  }
}

module B {
  import A
}

module C0 {}

module C refines C0 {
  import B
}

module CC refines C {}

module D refines CC {
  import A = B.A
}

module E {
  import S = A.X // error
}

module F {
  import DD = D.A
}

module G {
  module H {
    module Z {
      const z := 52
    }
  }

  module I {
    module J {
      import E.S.AAA // S is an error
    }
    module K {
      import H.Y  // error
    }
    module L {
    }
  }
}
