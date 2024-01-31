// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// Demonstrates that nested comments don't work with */ in line comment

method m() {
/*
  var b: int;
  // */
  var c: int;
*/
}
