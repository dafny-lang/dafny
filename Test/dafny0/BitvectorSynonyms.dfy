// RUN: %dafny /compile:0 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Z(a: bv0, b: bv0) returns (c: bv0, d: bv10)
{
  c := a & b;
  c := c | b;
  c :=  !c;
  c := a + c;
  assert c == 0;
  d := c as bv10;
  assert c as int == 0;
}

method S(a: bv10, b: bv10) returns (c: bv18)
{
  var d := a | !a;
  assert (!d) as int == 0;
  assert d >= !d;
  d := a & a;
  d := !d;
  c := (d << 8) as bv18;
  assert 2*c == c + c;
}

