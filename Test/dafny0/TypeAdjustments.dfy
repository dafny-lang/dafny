// RUN: %exits-with 4 %dafny /compile:0 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Even = u | u % 2 == 0

method M0(n: nat, e: Even) {
  var x; // nat
  x := n;
  x := n;

  var y; // int
  y := e;
  y := n;

  var z; // int
  z := n + n;

  x, y, z := *, *, *;
  if {
  case true =>
    assert 0 <= x;
  case true =>
    assert 0 <= y; // error: y is an int
  case true =>
    assert y % 2 == 0; // error: y is an int
  case true =>
    assert 0 <= z; // error: z is an int
  }
}
