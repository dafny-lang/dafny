// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


method z(x: string, y: string) {
  var a: string := "abc";
  var b: string := x + y;
  assert a <= x ==> a < b; // SHOULD FAIL
}