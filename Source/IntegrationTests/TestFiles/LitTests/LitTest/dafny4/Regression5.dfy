// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


type Syn = bv8

method P(x: int) returns (y: bv8)
  requires x < 256
{
  y := x as Syn;  // error: value might be negative
}

method Q() {
  var r: int := -3;
  var v: bv8;
  v := r as bv8;  // error: value most certainly is negative
}
