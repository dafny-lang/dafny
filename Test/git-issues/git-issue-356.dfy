// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test(b: bv32, n: nat, c: char)
  requires b < 0x1_0000
  requires n < 0x1_0000
{
  var r: real := 42.0;
  var ch: char;
  ch := c as char;
  ch := n as char;  // translates into char#FromInt(n), which is good
  ch := b as char;  // translates into nat_from_bv32(b), which crashes; should be char#FromInt(nat_from_bv32(b))
  ch := r as char;

  var nn: int;
  var nnn: int;
  nn := c as int;
  nn := r as int;
  nn := b as int;
  nn := nnn as int;

  var rr: real;
  //rr := c as real;
  rr := c as int as real;
  rr := n as real;
  rr := b as real;
  rr := r as real;

  var bb: bv32;
  //bb := c as bv32;
  bb := c as int as bv32;
  bb := n as bv32;
  bb := r as bv32;
  bb := b as bv32;
  assert true;
}
