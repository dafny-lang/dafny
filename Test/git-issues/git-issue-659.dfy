// RUN: %baredafny verify %args "%s" > "%t"
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

module X {
  import I = A.Inner`P
  method m() {
    assert I.a == 10;
    assert I.c == 30;
  }
}

module Y {
  import I = A.Inner`{P,Q}
  method m() {
    assert I.a == 10;
    assert I.b == 20;
  }
}

