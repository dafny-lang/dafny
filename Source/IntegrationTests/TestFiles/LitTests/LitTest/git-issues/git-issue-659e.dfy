// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M {
  module Inner {
    export P reveals a,c
    export Q reveals b,c
    const a := 10
    const b := 20
    const c := 30
  }
}

module X {
  import I = M.Inner`Q
  method m() {
    assert I.a == 10; // error -- no a in Q
    assert I.c == 30;
  }
}

module Z {
  module A {}
  module B {}
  export A provides A
  export B provides B
}

module T {
  import Z.A  // error -- Z has no default export
}

module Y {
  module A {}
  module B {
    const b := 10
  }
  export A provides A
  export Y provides B
}

module TY {
  import YB = Y.B  // OK - Y has a default export set
  const b := YB.b
}
