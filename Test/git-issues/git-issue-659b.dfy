// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module Inner {
    export P reveals a,c
    export Q reveals b,c
    const a := 10
    const b := 20
    const c := 30
  }
}

module Z {
  import I = A.Inner`P
  import J = A.Inner`Q
  method m() {
    assert I.a == 10;
    assert I.b == 20; // error
  }
}

module B {
  export P reveals a,c
  export Q reveals b,c
  const a := 10
  const b := 20
  const c := 30
}

module Y {
  import I = B`P
  import J = B`Q
  method m() {
    assert I.a == 10;
    assert I.b == 20; // error
  }
}

