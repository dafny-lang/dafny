// RUN: %exits-with 4 %dafny /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Syn = bv8

method P(x: int) returns (y: bv8)
  requires x < 256
{
  y := x as Syn;  // error: value might be negative
}

method Q() {
  var r: real := -3.0;
  var v: bv8;
  v := r as bv8;  // error: value most certainly is negative
}
