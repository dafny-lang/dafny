// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method z(x: string, y: string) {
  var a: string := "abc";
  var b: string := x + y;
  assert a <= x ==> a < b; // SHOULD FAIL
}