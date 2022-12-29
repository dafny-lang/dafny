// RUN: %dafny /compile:0 /print:"%t.print" /rprint:- /env:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
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
  print t, " ", u, " ", v, "\n";
  DoArith32();
  var unry := Unary(5);
  print "bv16: 5 - 2 == ", unry, "\n";
  unry := Unary(1);
  print "bv16: 1 - 2 == ", unry, "\n";

  SummoTests();

  var zz0;
  var zz1 := Bv0Stuff(zz0, 0);
  print zz0, " ", zz1, "\n";
  print zz0 < zz1, " ", zz0 <= zz1, " ", zz0 >= zz1, " ", zz0 > zz1, "\n";

  TestCompilationTruncations();

  Shifts();

	Rotates();
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
  print b / 3, " ", b % 4, "\n";
}

method Bv0Stuff(x: bv0, y: bv0) returns (z: bv0)
  ensures z == 0  // after all, there is only one value
{
  // This will make sure verification and compilation won't crash for these expressions
  z := x + y;
  z := x * z - y;
  z := (x ^ z) | (y & y);
  z := !z + -z;
}

// --------------------------------------

method TestCompilationTruncations()
{
  M67(-1, 3);
  M64(-1, 3);
  M53(-1, 3);
  M33(-1, 3);
  M32(-1, 3);
  M31(-1, 3);
  M16(-1, 3);
  M15(-1, 3);
  M8(-1, 3);
  M6(-1, 3);
  M1(1, 1);
  M0(0, 0);

  P2(3, 2);
}

method M67(a: bv67, b: bv67)
{
  print "bv67:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M64(a: bv64, b: bv64)
{
  print "bv64:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M53(a: bv53, b: bv53)
{
  print "bv53:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M33(a: bv33, b: bv33)
{
  print "bv33:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M32(a: bv32, b: bv32)
{
  print "bv32:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M31(a: bv31, b: bv31)
{
  print "bv31:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M16(a: bv16, b: bv16)
{
  print "bv16:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M15(a: bv15, b: bv15)
{
  print "bv15:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M8(a: bv8, b: bv8)
{
  print "bv8:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M6(a: bv6, b: bv6)
{
  print "bv6:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M1(a: bv1, b: bv1)
{
  print "bv1:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method M0(a: bv0, b: bv0)
{
  print "bv0:  ", a, " + ", b, " == ", a+b, "     - ", b, " == ", -b, "     !! ", b, " == ! ", !b, " == ", !!b, "\n";
}

method P2(a: bv2, b: bv2)
  requires b != 0
{
  print "bv2:\n";
  print "  ", a, " + ", b, " == ", a+b, "\n";
  print "  ", a, " - ", b, " == ", a-b, "\n";
  print "  ", a, " * ", b, " == ", a*b, "\n";
  print "  ", a, " / ", b, " == ", a/b, "\n";
  print "  ", a, " % ", b, " == ", a%b, "\n";
}

newtype Handful = x | 0 <= x < 0x50

method Shifts()
{
  var x: int, h: Handful, b67: bv67, w: bv32, seven: bv7, bb: bv2, noll: bv0;
  x, h := 3, 3;

  b67, w, seven := 5, 5, 5;
  PrintShifts("bv67", b67, 8 * b67, b67 << x, b67 << h);
  PrintShifts("bv32", w, 8 * w, w << x, w << h);
  PrintShifts("bv7", seven, 8 * seven, seven << x, seven << h);
  bb, x, h := 1, 1, 1;
  PrintShifts("bv2", bb, 2 * bb, bb << x, bb << h);
  x, h := 0, 0;
  PrintShifts("bv0", noll, 0 * noll, noll << x, noll << h);

  b67, w, bb, noll := 0x4_0000_0000_0000_0001, 1, 1, 0;
  var One67: bv67 := 1;
  PrintShifts("bv67 again", b67 << One67, b67 << w, b67 << bb, b67 << noll);  // 2, ...
  b67, w, bb, noll := 2, 0xC000_0000 + 2000, 1, 0;
  var Two32: bv32 := 2;
  PrintShifts("bv32 again", w << b67, w << Two32, w << bb, w << noll);  // 8000, ...
  seven, b67, w, bb, noll := 127, 2, 2, 2, 0;
  PrintShifts("bv7 again", seven << b67, seven << w, seven << bb, seven << noll);  // 124, ...
  b67, w, bb := 0, 0, 0;
  PrintShifts("bv0 again", noll << b67, noll << w, noll << bb, noll << noll);  // 0, ...
}

method PrintShifts<T>(s: string, a: T, b: T, c: T, d: T)
{
  print "PrintShifts: ", s, ": ", a, " ", b, " ", c, " ", d, "\n";
}

method Rotates()
{
  var x: int, w: bv12, seven: bv7, bb: bv2, noll: bv0;
  x := 3;

  w, seven, noll :=  5, 5, 0;
  PrintRotates("bv12", w, w.RotateLeft(x).RotateRight(x));
  PrintRotates("bv7", seven, seven.RotateLeft(x).RotateRight(x));
  bb, x := 1, 1;
  PrintRotates("bv2", bb, bb.RotateLeft(x).RotateRight(x));
  x := 0;
  PrintRotates("bv0", noll, noll.RotateLeft(x).RotateRight(x));
	x := 5;
  w, seven := 0xC00 + 2000, 127;
  PrintRotates("bv12 again", w, w.RotateLeft(x).RotateRight(x));
  PrintRotates("bv7 again", seven, seven.RotateLeft(x).RotateRight(x));
}

method PrintRotates<T>(s: string, a: T, b: T)
{
  print "PrintRotates: ", s, ": ", a, " ", b, "\n";
}
