// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
