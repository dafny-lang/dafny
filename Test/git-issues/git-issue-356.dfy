// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test(b: bv32, n: nat, r: real, c: char)
  requires b < 0x1_0000
  requires n < 0x1_0000
{
  var rr: real := 42.0;
  var ch: char;
  ch := n as char;  // translates into char#FromInt(n), which is good
  ch := b as char;  // translates into nat_from_bv32(b), which crashes; should be char#FromInt(nat_from_bv32(b))
  ch := rr as char;
  assert true;
}
