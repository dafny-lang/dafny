// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module B
  const c: int := B.c
  method m() {
    assert c == 10;
  }
}

// No value to find
