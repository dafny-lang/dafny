// RUN: %dafny /env:0 /dprint:- /dafnyVerify:0 "%s" > "%t"
// RUN: %dafny /env:0 /rprint:- /compile:3 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Outer.Test();
  XY.Test();
  U.V.Test();
  print MyModule.Q.W.E.R.T.Y.h, "\n";
}

// ----- Outer

module Outer {
  module C {
    import D
    const c := 2 + D.d
  }
  method Test() {
    print A.a, " ", B.b, " ", C.c, " ", D.d, "\n";  // 6 1 5 3
  }
}

module Outer.A {
  import B
  import C
  const a := B.b + C.c
}

module Outer.B {
  const b := 1
}

module Outer.D {
  const d := 3
}

// ----- Oreo

module XY.X {
  const m := 20
  module M {
    import Y
    const n := Y.m - 5
  }
}

module XY {
  method Test() {
    print X.m, " ", X.M.n, " ", Y.m, "\n";  // 20 17 22
  }
}

module XY.Y {
  const m := 22
}

// ----- Triple

module U.V.W.X {
  const x0 := 12
}

module U.V {
  const x2 := 14 + W.x1 + W.X.x0
  method Test() {
    print W.X.x0, " ", W.x1, " ", x2, "\n";  // 12 144 170
  }
}

module U.V.W {
  const x1 := 12 * X.x0
}

// ----- Prefix-named modules in user-defined module

module MyModule {
  module Q.W.E.R.T {
  }
  module Q.W.E.R.T.Y {
    const h := 2;
  }
}
