// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
    assert I.a == 10;
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
