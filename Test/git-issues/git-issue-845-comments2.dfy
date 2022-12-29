// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Demonstrates that nested comments don't work with */ in strings

method m() {
/*
  var b: int;
  var s: string := "a*/b";
  var c: int;
*/
}
