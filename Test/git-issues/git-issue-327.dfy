// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module AA {
    module AAA {
      const aaa := 50
    }
  }
  const a := 51
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
  import S = A.AA
}

module F {
  import DD = D.A
  method m() { assert DD.a == 51; }
}

module G {
  module H {
    module Z {
      const z := 52
    }
  }

  module I {
    module J {
      import E.S.AAA
      import HH = H.Z
      import D.A
      import D.A.AA
      import F
      method m0() { assert AAA.aaa == 50; }
      method m1() { assert HH.z == 52; }
      method m2() { assert A.a == 51; }
      method m3() { assert AA.AAA.aaa == 50; }
    }
    module K {
    }
  }
}
