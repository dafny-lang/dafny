// RUN: %exits-with 0 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  const c: int := B.c
  method m() {
    assert c == 10;
  }
}

module A.B {
  const c := 10;
}

// Checks for warning if there is no companion body-less declaration
