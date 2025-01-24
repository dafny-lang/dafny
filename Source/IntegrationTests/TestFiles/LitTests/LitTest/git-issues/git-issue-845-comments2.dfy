// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// Demonstrates that nested comments don't work with */ in strings

method m() {
/*
  var b: int;
  var s: string := "a*/b";
  var c: int;
*/
}
