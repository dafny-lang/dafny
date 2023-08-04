// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Subset tsype conversions

type Tx = x | 0 <= x <= 100
method TestD(x: Tx) {
  var z := x as Tx;
  var c := x as char;
  var n := x as int;
  var r := x as real;
  var b := x as bv8;
  var o := x as ORDINAL;
}
method TestF(cc: char, nn: int, rr: real, bb: bv8, oo: ORDINAL) {
  var xx: Tx;
  xx := oo as Tx; // ERROR
  xx := cc as Tx; // ERROR
  xx := nn as Tx; // ERROR
}
method TestG(cc: char, nn: int, rr: real, bb: bv8, oo: ORDINAL) {
  var xx: Tx;
  xx := rr as Tx; // ERROR
  xx := bb as Tx; // ERROR
}
