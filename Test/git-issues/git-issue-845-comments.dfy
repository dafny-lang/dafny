// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Demonstrates that nested comments don't work with */ in line comment

method m() {
/*
  var b: int;
  // */
  var c: int;
*/
}
