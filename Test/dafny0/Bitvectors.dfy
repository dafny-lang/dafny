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
  DoArith32();
  var unry := Unary(5);
  print "bv16: 5 - 2 == ", unry, "\n";
  unry := Unary(1);
  print "bv16: 1 - 2 == ", unry, "\n";
  SummoTests();
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

method DoArith32() {
  var r, s := Arithmetic(65, 120);
  print r, " ", s, "\n";
  var x, y := 0x7FFF_FFFF, 0x8000_0003;
  r, s := Arithmetic(x, y);
  assert r == 2 && s == 4;
  print r, " ", s, "\n";
  assert x < y && x <= y && y >= x && y > x;
  print "Comparisons: ", x < y, " ", x <= y, " ", x >= y, " ", x > y, "\n";
}

method Unary(x: bv16) returns (y: bv16)
  ensures y == x - 2
{
  // This method takes a long time (almost 20 seconds) to verify
  y := -(-!-!!--(x));
  y := !-y;
  var F := 0xffff;
  calc {
    y;
    !--(-!-!!--(x));
    F - ---!-!!--x;
    { assert ---!-!!--x == -!-!!--x; }
    F - -!-!!--x;
    F + !-!!--x;
    F + F - -!!--x;
    F + F + !!--x;
    { assert !!--x == --x == x; }
    F + F + x;
    x - 2;
  }
}

method SummoTests() {
  var a: bv64 := 5;
  a := 2 * 2 * 2 * (2 * 2) * a * 2 * (2 * 2 * 2) * 2;  // shift left 10 bits
  var b := a / 512;  // b is a shifted right 9 bits, so it is 5 shifted left 1 bit
  assert b == 10;
  assert b / 3 == 3 && b / 4 == 2;
  assert b % 3 == 1 && b % 4 == 2;
  print b / 3, " ", b % 4;
}
