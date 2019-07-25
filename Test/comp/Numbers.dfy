// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Literals();
  Arithmetic();
  PrintReals();
  SimpleReality();
  BitVectorTests();
  MoreBvTests();
  NewTypeTest();
  OrdinalTests();
}

method Print(description: string, x: int) {
  print x;
  if |description| != 0 {  // string length (that is, sequence length)
    print " (aka ", description, ")";
  }
  print "\n";
}

method PrintReal(description: string, x: real) {
  print x;
  if description != "" {  // string comparison
    print " (aka ", description, ")";
  }
  print "\n";
}

method PrintSeq(s: seq) {
  var sep, i := "", 0;
  while i < |s| {
    print sep, s[i];
    sep := " ";
    i := i + 1;
  }
  print "\n";
}

method Literals() {
  Print("", 0);
  Print("", -0);
  Print("", 3);
  Print("", -5);

  Print("C# int.MaxValue", 0x7FFF_ffff);  // int.MaxValue
  Print("2^31", 0x8000_0000);  // int.MaxValue + 1
  Print("", 0x8000_0001);  // int.MaxValue + 2
  Print("C# uint.MaxValue", 0xFFFF_FFFF);  // uint.MaxValue
  Print("2^32", 0x1_0000_0000);  // uint.MaxValue + 1
  
  Print("JavaScript Number.MAX_SAFE_INTEGER", 0x1F_FFFF_FFFF_FFFF_FFFF);  // 2^53 -  1
  Print("2^53", 0x20_0000_0000_0000_0000);  // 2^53
  Print("JavaScript Number.MAX_SAFE_INTEGER", - 0x1F_FFFF_FFFF_FFFF_FFFF);  // - (2^53 -  1)
  Print("", - 0x20_0000_0000_0000_0000);  // - 2^53

  Print("C# long.MaxValue", 0x7FFF_ffff_FFFF_ffff);  // long.MaxValue
  Print("2^63", 0x8000_0000_0000_0000);  // long.MaxValue + 1
  Print("", 0x8000_0000_0000_0001);  // long.MaxValue + 2
  Print("C# ulong.MaxValue", 0xFFFF_FFFF_FFFF_FFFF);  // ulong.MaxValue
  Print("2^64", 0x1_0000_0000_0000_0000);  // ulong.MaxValue + 1

  Print("2^100", 0x10_0000_0000_0000_0000_0000_0000);  // 2^100
  Print("M_39", 170_141_183_460_469_231_731_687_303_715_884_105_727);

  PrintReal("", 0.0);
  PrintReal("", -0.0);
  PrintReal("", 3.0);
  PrintReal("", -5.0);
  PrintReal("", 3.14);
  PrintReal("", -2.71);
  PrintReal("a billion", 1_000_000_000.0);
  PrintReal("G", 0.000_000_000_066_740_8);
  PrintReal("G", 6.67408 / 100_000_000_000.0);
  PrintReal("G", 6.67408 * 0.000_000_000_01);
  PrintReal("1/10 of M_39", 17_014_118_346_046_923_173_168_730_371_588_410_572.7);  // test a large mantissa
  PrintReal("1/googol", 0.000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_1);
}

method Arithmetic() {
  PrintSeq([31 + 4, 31 - 4, 4 - 31]);  // also tests sequence displays

  PrintSeq([31 * 4, 31 * -4]);
  PrintSeq([-31 * 4, -31 * -4]);
  
  PrintSeq(['3' + '4', '7' - '4' + 'N', '4' - '3' + '1']);

  DivMod(31, 4);
  DivMod(-31, 4);
  DivMod(31, -4);
  DivMod(-31, -4);
  DivMod(0, 4);
  DivMod(0, -4);

  PrintSeq([0.3 - 0.1]);  // should be 0.2, not something like 0.19999999999999998
  PrintSeq([31.2 + 4.0, 31.2 - 4.0, 4.0 - 31.2]);

  PrintSeq([31.2 * 4.0, 31.2 * -4.0]);
  PrintSeq([-31.2 * 4.0, -31.2 * -4.0]);

  DivModReal(31.2, 4.0);
  DivModReal(-31.2, 4.0);
  DivModReal(31.2, -4.0);
  DivModReal(-31.2, -4.0);
}

method DivMod(dividend: int, divisor: int)
  requires divisor != 0
{
  // Dafny uses Euclidean division/modulo, so the remainder is always non-negative
  var quotient := dividend / divisor;
  var remainder := dividend % divisor;
  assert 0 <= remainder;
  assert quotient * divisor + remainder == dividend;
  print quotient, " ", remainder, " ", quotient * divisor + remainder, "\n";
}

method DivModReal(dividend: real, divisor: real)
  requires divisor != 0.0
{
  var quotient := dividend / divisor;
  assert quotient * divisor == dividend;
  print quotient, " ", quotient * divisor, "\n";
}

method PrintReals() {
  // 0
  P(0.0);
  P(0.2 + 0.4 - 0.6);
  var r: real;
  P(r);
  print "\n";

  // integer
  P(120.0);
  P(000120.0);
  P(20.0 / 3.0 + 4.0 / 3.0);  // 8.0
  P(-(20.0 / 3.0 + 4.0 / 3.0));  // -8.0
  print "\n";

  // decimal digits
  P(123.4567);
  P(-123.4567);
  P(0.1234);
  P(-0.1234);
  P(2.0 / 3.0 + 0.4 / 3.0);  // 0.8
  print "\n";
  P(0.2);
  P(0.02);
  P(0.0_0002);
  print "\n";
  P(-0.2);
  P(-0.02);
  P(-0.0_0002);
  print "\n";

  // general
  P(20.0 / 3.0);
  P(-20.0 / 3.0);
  P(20.0 / -3.0);
  P(-20.0 / -3.0);
  print "\n";
}

method P(r: real) {
  print r, " ";
}

method SimpleReality() {
  var r: real;
  var z := r - r;
  var s := 0.81;
  var t := 2.0 * s + z - s;
  var u := s / t;  // 1.0
  print r, " ", z, " ", s, " ", t, " ", u, "\n";
  print s == t, " ", z == u, "\n";
}

method BitVectorTests() {
  var a: bv0 := 0;
  var b: bv1 := 0;
  var c: bv2 := 2;
  var d: bv7 := 2;
  var e: bv8 := 2;
  var f: bv15 := 2;
  var g: bv16 := 2;
  var h: bv53 := 2;
  var i: bv100 := 2;
  print a, " ", c, " ", h, " ", i, "\n";
  a, c, h, i := a + a, c + 1, 3 * h, i * 23;
  print a, " ", c, " ", h, " ", i, "\n";
  a, c, h, i := a * a, c * c, h * h, i * i;
  print a, " ", c, " ", h, " ", i, "\n";
  a, c, h, i := a - a, c - c, h - h, i - i;
  print a, " ", c, " ", h, " ", i, "\n";

  NativeBv32();
  NativeBv53();
}

method NativeBv32() {
  var x: bv32 := 0;
  var y: bv32 := 15;
  x := x + y + y - x + 1;  // 2*y + 1
  y := x / y;  // 2
  x := x - y;  // 29
  var z: bv32 := 17;
  z := z % 3;  // 2
  var w0: bv32 := -13;  // wrap backwards
  var w1 := w0 + 15;  // wrap forwards
  print x, " ", y, " ", z, " ", w0, " ", w1, "\n";
}

method NativeBv53() {
  var x: bv53 := 0;
  var y: bv53 := 15;
  x := x + y + y - x + 1;  // 2*y + 1
  y := x / y;  // 2
  x := x - y;  // 29
  var z: bv53 := 17;
  z := z % 3;  // 2
  var w0: bv53 := -13;  // wrap backwards
  var w1 := w0 + 15;  // wrap forwards
  print x, " ", y, " ", z, " ", w0, " ", w1, "\n";
}

type MyBv = x: bv4 | 2 <= x < 10 witness 7

method MoreBvTests() {
  var u: bv0;
  var w: bv32;
  var B: bv100;
  var m: MyBv;
  u := 0;
  w := 0;
  B := 0;
  m := 9;
  u := u + u & u;
  print u, " ", w, " ", B, " ", m, "\n";
  u, w, B, m := u | 0, w | 0, B | 0, m | 0;
  print u, " ", w, " ", B, " ", m, "\n";
  u, w, B, m := u ^ 0, w ^ 0, B ^ 0, m ^ 0;
  print u, " ", w, " ", B, " ", m, "\n";
  u, w, B, m := !u, !w, !B, !m;
  print u, " ", w, " ", B, " ", m, "\n";
  
  B := 32;
  B := B << 2;  // 128
  B := B >> 4;  // 8
  m := 2;
  m := m << 2;  // 8
  m := m >> 1;  // 4
  print B, " ", m, "\n";
  
  B := 32 | 4;
  B := B.RotateLeft(99);  // 16 | 2
  var B' := B;
  B := B.RotateRight(98);  // 64 | 8
  m := 2;
  m := m.RotateLeft(2);  // 8
  m := m.RotateRight(1);  // 4
  print B', " ", B, " ", m, "\n";  // 18 72 4

  u := u.RotateLeft(0).RotateRight(0);
  print u, "\n";  // as 0 as ever
}

newtype {:nativeType "number"} MyNumber = x | -100 <= x < 0x10_0000_0000

method NewTypeTest() {
  var a, b := 200, 300;
  var r0 := M(a, b);
  var r1 := M(b, a);
  var r2 := M(-2, b);
  print a, " ", b, "\n";
  print r0, " ", r1, " ", r2, "\n";
}

method M(m: MyNumber, n: MyNumber) returns (r: MyNumber) {
  if m < 0 || n < 0 {
    r := 18;
  } else if m < n {
    r := n - m;
  } else {
    r := m - n;
  }
}

method OrdinalTests() {
  PrintOrdinalInfo(0);
  PrintOrdinalInfo(1);
  PrintOrdinalInfo(42);
}

method PrintOrdinalInfo(o : ORDINAL) {
  print o;
  print ": IsNat: ", o.IsNat;
  print ", Offset: ", o.Offset;
  print ", IsLimit: ", o.IsLimit;
  print ", IsSucc: ", o.IsSucc, "\n";
}
