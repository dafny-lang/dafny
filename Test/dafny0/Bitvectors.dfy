// RUN: %dafny /compile:3 /print:"%t.print" /rprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M(a: bv1, b: bv32) returns (c: bv32, d: bv1)
{
  c := b;
  d := a;
  var x := 5000;
  c := x;
  var y := 4000;
  y := c;
}

method Main() {
  var x := 4000;
  var y := 4000;
  var z: bv32;
  var w: bv32;
  if x == y {
    z := x;
  } else {
    w := y;
  }
  print x, " ", y, " ", z, " ", w, "\n";
  var t, u, v := BitwiseOperations();
  print t, " ", v, " ", v, "\n";
  MoreMain();
}

method BitwiseOperations() returns (a: bv47, b: bv47, c: bv47)
{
  b, c := 2053, 1099;
  a := b & c;
  a := a | a | (b & b & c & (a ^ b ^ c) & a);
}

method Arithmetic(x: bv32, y: bv32) returns (r: bv32, s: bv32)
  ensures r == x + y && s == y - x
{
  r := x + y;
  s := y - x;
}

method MoreMain() {
  var r, s := Arithmetic(65, 120);
  print r, " ", s, "\n";
  var x, y := 0x7FFF_FFFF, 0x8000_0003;
  r, s := Arithmetic(x, y);
  assert r == 2 && s == 4;
  print r, " ", s, "\n";
  assert x < y && x <= y && y >= x && y > x;
  print "Comparisons: ", x < y, " ", x <= y, " ", x >= y, " ", x > y, "\n";
}
