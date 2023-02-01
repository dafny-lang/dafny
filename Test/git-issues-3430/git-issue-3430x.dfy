// RUN: %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module B
  const c: int := B.c
  method m() {
    assert c == 10;
  }
}

module A.B {
  const c := 10;
}

module X
