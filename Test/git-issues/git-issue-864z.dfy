// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export reveals a
  const a := 10
  const b := 20
}

module B refines A {
  export reveals *
  const c := 30
}

module C {
  import B
  method m() {
    assert B.c == 30;
    assert B.a == 10;
    assert B.b == 20;
  }
}

module D {
  import B`A
  method m() {
    assert B.c == 30; // error
    assert B.a == 10;
    assert B.b == 20; // error
  }
}

