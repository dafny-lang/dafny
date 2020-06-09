// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test(b: bv32, n: nat, r: real, c: char)
  requires b < 0x1_0000
  requires n < 0x1_0000
{
  var ch: char;
  ch := r as char;
  assert true;
}
