// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module LiteralSizes {
  method M(a: bv1, b: bv32) returns (c: bv32, d: bv1)
  {
    c := b;
    d := a;
    var x := 5000;  // error: number too big
    d := x;
    var y := 4000;
    y := c;
    var z: bv0;
    z := 0;
    z := 1;  // error: number too big
    c := 0x8000_0000;
    c := 0xFFFF_FFFF;
    c := 0x1_0000_0000;  // error: number too big
  }
}
