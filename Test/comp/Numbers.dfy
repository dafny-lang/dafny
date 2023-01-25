// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  Literals();
  Arithmetic();
  PrintReals();
  SimpleReality();
  BitVectorTests();
  MoreBvTests();
  NativeTypeTest();
  NewTypeTest();
  OrdinalTests();
  ZeroComparisonTests();
  TestConversions();
  ComparisonRegressions();
  CastRegressions();
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

  Print("JavaScript Number.MAX_SAFE_INTEGER", 0x1F_FFFF_FFFF_FFFF);  // 2^53 -  1
  Print("2^53", 0x20_0000_0000_0000);  // 2^53
  Print("JavaScript Number.MIN_SAFE_INTEGER", - 0x1F_FFFF_FFFF_FFFF);  // - (2^53 -  1)
  Print("", - 0x20_0000_0000_0000);  // - 2^53

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
  DivModNative();

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

newtype uint8 = x | 0 <= x < 0x100
newtype uint16 = x | 0 <= x < 0x1_0000
newtype uint32 = x | 0 <= x < 0x1_0000_0000
newtype uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000
newtype int8 = x | -0x80 <= x < 0x80
newtype int16 = x | -0x8000 <= x < 0x8000
newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method DivModNative() {
  // For non-negative operands, Euclidean division and moduus coincide with those of the
  // target languages. Here, we're testing that no bad conversion happens between large
  // unsigned integers and the same-bitpattern negative signed integer.
  print "uint8:  ";
  TestDivModUint8(0xE7, 23, " ");                                        // (10, 1)
  TestDivModUint8(0xE7, 0xFF, "\n");                                     // (0, 231)
  print "uint16: ";
  TestDivModUint16(0xFFE7, 23, " ");                                     // (2848, 7)
  TestDivModUint16(0xFFE7, 0xFFFF, "\n");                                // (0, 65511)
  print "uint32: ";
  TestDivModUint32(0xFFFF_FFE7, 23, " ");                                // (186_737_707, 10)
  TestDivModUint32(0xFFFF_FFE7, 0xFFFF_FFFF, "\n");                      // (0, 4_294_967_271)
  print "uint64: ";
  TestDivModUint64(0xFFFF_FFFF_FFFF_FFE7, 23, " ");                      // (802_032_351_030_850_069, 4)
  TestDivModUint64(0xFFFF_FFFF_FFFF_FFE7, 0xFFFF_FFFF_FFFF_FFFF, "\n");  // (0, 18_446_744_073_709_551_591)

  // Compute via defining definitions
  var i, j := 103, 13;
  print "via real: ";
  EuclideanDefinitions(i, j, " ");       // 7:12
  EuclideanDefinitions(-i, j, " ");      // -8:1
  EuclideanDefinitions(i, -j, " ");      // -7:12
  EuclideanDefinitions(-i, -j, "\n");    // 8:1

  // Check with SMT
  assert i / j == 7       && i % j == 12;       // (7, 12)
  assert (-i) / j == -8   && (-i) % j == 1;     // (-8, 1)
  assert i / (-j) == -7   && i % (-j) == 12;    // (-7, 12)
  assert (-103) / (-j) == 8 && (-i) % (-j) == 1;  // (8, 1)
  // NOTE: In the previous line, if "-103" is replaced by the equivalent "-i", then Z3 version 4.8.4
  // complains. In fact, Z3 4.8.4 is then happy to prove "(-i) / (-j) == 7", which is bogus. However,
  // it seems that this error has been corrected in Z3 4.8.7 (or earlier). Therefore, by just
  // writing "-103" here, we have a workaround for this test file. Once Dafny switches to a version
  // of Z3 that is 4.8.7 or newer, then it would be good to switch "-103" back to "-i" here to make
  // sure that particular Z3 bug has been fixed.

  print "int:      ";
  TestDivModInt(i, j, " ");                    // (7, 12)
  TestDivModInt(-i, j, " ");                   // (-8, 1)
  TestDivModInt(i, -j, " ");                   // (-7, 12)
  TestDivModInt(-i, -j, " ");                  // (8, 1)
  TestDivModInt(-108, 9, " ");                 // (-12, 0)
  TestDivModInt(-108, -9, "\n");               // (12, 0)

  // Test for native integers
  var i8: int8, j8: int8 := 103, 13;
  var i16: int16, j16: int16 := 103, 13;
  var i32: int32, j32: int32 := 103, 13;
  var i64: int64, j64: int64 := 103, 13;
  print "int8:     ";
  TestDivModInt8(i8, j8, " ");                       // (7, 12)
  TestDivModInt8(-i8, j8, " ");                      // (-8, 1)
  TestDivModInt8(i8, -j8, " ");                      // (-7, 12)
  TestDivModInt8(-i8, -j8, " ");                     // (8, 1)
  TestDivModInt8(-108, 9, " ");                      // (-12, 0)
  TestDivModInt8(-108, -9, "\n");                    // (12, 0)
  print "int16:    ";
  TestDivModInt16(i16, j16, " ");                    // (7, 12)
  TestDivModInt16(-i16, j16, " ");                   // (-8, 1)
  TestDivModInt16(i16, -j16, " ");                   // (-7, 12)
  TestDivModInt16(-i16, -j16, " ");                  // (8, 1)
  TestDivModInt16(-108, 9, " ");                     // (-12, 0)
  TestDivModInt16(-108, -9, "\n");                   // (12, 0)
  print "int32:    ";
  TestDivModInt32(i32, j32, " ");                    // (7, 12)
  TestDivModInt32(-i32, j32, " ");                   // (-8, 1)
  TestDivModInt32(i32, -j32, " ");                   // (-7, 12)
  TestDivModInt32(-i32, -j32, " ");                  // (8, 1)
  TestDivModInt32(-108, 9, " ");                     // (-12, 0)
  TestDivModInt32(-108, -9, "\n");                   // (12, 0)
  print "int64:    ";
  TestDivModInt64(i64, j64, " ");                    // (7, 12)
  TestDivModInt64(-i64, j64, " ");                   // (-8, 1)
  TestDivModInt64(i64, -j64, " ");                   // (-7, 12)
  TestDivModInt64(-i64, -j64, " ");                  // (8, 1)
  TestDivModInt64(-108, 9, " ");                     // (-12, 0)
  TestDivModInt64(-108, -9, "\n");                   // (12, 0)
}
function method Sign(n: int): int {
  if n < 0 then -1 else if n == 0 then 0 else 1
}
function method Abs(n: int): nat {
  if n < 0 then -n else n
}
method EuclideanDefinitions(i: int, j: int, suffix: string)
  requires j != 0
{
  // For integers i and j, Euclidean division (i/j) and modulus (i%j) are defined as follows:
  //   i/j    =    Sign(j) * Floor(i // Abs(j))   where "//" denotes real division
  //   i%j    =    i - |j| * Floor(i // Abs(j))   where "//" denotes real division
  var div := Sign(j) * (i as real / Abs(j) as real).Floor;
  var mod := i - Abs(j) * (i as real / Abs(j) as real).Floor;
  print div, ":", mod, suffix;
}
method TestDivModInt(a: int, b: int, suffix: string) requires b != 0 {
  print a / b, ":", a % b, suffix;
}
method TestDivModUint8(a: uint8, b: uint8, suffix: string) requires b != 0 {
  print a / b, ":", a % b, suffix;
}
method TestDivModUint16(a: uint16, b: uint16, suffix: string) requires b != 0 {
  print a / b, ":", a % b, suffix;
}
method TestDivModUint32(a: uint32, b: uint32, suffix: string) requires b != 0 {
  print a / b, ":", a % b, suffix;
}
method TestDivModUint64(a: uint64, b: uint64, suffix: string) requires b != 0 {
  print a / b, ":", a % b, suffix;
}
method TestDivModInt8(a: int8, b: int8, suffix: string) requires b != 0 && -127 <= a {
  print a / b, ":", a % b, suffix;
}
method TestDivModInt16(a: int16, b: int16, suffix: string) requires b != 0 && -0x7FFF <= a {
  print a / b, ":", a % b, suffix;
}
method TestDivModInt32(a: int32, b: int32, suffix: string) requires b != 0 && -0x7FFF_FFFF <= a {
  print a / b, ":", a % b, suffix;
}
method TestDivModInt64(a: int64, b: int64, suffix: string) requires b != 0 && -0x7FFF_FFFF_FFFF_FFFF <= a {
  print a / b, ":", a % b, suffix;
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

newtype {:nativeType "number", "long"} NativeType = x | -100 <= x < 0x10_0000_0000

method NativeTypeTest() {
  var a, b := 200, 300;
  var r0 := M(a, b);
  var r1 := M(b, a);
  var r2 := M(-2, b);
  print a, " ", b, "\n";
  print r0, " ", r1, " ", r2, "\n";
}

method M(m: NativeType, n: NativeType) returns (r: NativeType) {
  if m < 0 || n < 0 {
    r := 18;
  } else if m < n {
    r := n - m;
  } else {
    r := m - n;
  }
}

newtype NewType = x: int | true

method NewTypeTest() {
  print var n: NewType := (-4) / (-2); n, "\n";
  print var n: NewType := ( 4) / (-2); n, "\n";
  print var n: NewType := (-4) / ( 2); n, "\n";
  print var n: NewType := ( 4) / ( 2); n, "\n";
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

method ZeroComparisonTests() {
  print "int:\n";
  ZCIntTests(-42);
  ZCIntTests(0);
  ZCIntTests(-0);
  ZCIntTests(23);

  print "NativeType:\n";
  ZCNativeTypeTests(-42);
  ZCNativeTypeTests(0);
  ZCNativeTypeTests(-0);
  ZCNativeTypeTests(23);
}

function method YN(b : bool) : string {
  if b then "Y" else "N"
}

method ZCIntTests(n : int) {
  print n, "\t",
    " <0 ",  YN(n < 0),  " <=0 ", YN(n <= 0),
    " ==0 ", YN(n == 0), " !=0 ", YN(n != 0),
    " >0 ",  YN(n > 0),  " >=0 ", YN(n >= 0),
    " 0< ",  YN(0 < n),  " 0<= ", YN(0 <= n),
    " 0== ", YN(0 == n), " 0!= ", YN(0 != n),
    " 0> ",  YN(0 > n),  " 0>= ", YN(0 >= n),
    "\n";
}

method ZCNativeTypeTests(n : NativeType) {
  print n, "\t",
    " <0 ",  YN(n < 0),  " <=0 ", YN(n <= 0),
    " ==0 ", YN(n == 0), " !=0 ", YN(n != 0),
    " >0 ",  YN(n > 0),  " >=0 ", YN(n >= 0),
    " 0< ",  YN(0 < n),  " 0<= ", YN(0 <= n),
    " 0== ", YN(0 == n), " 0!= ", YN(0 != n),
    " 0> ",  YN(0 > n),  " 0>= ", YN(0 >= n),
    "\n";
}

method TestConversions() {
  ConvertFromInt(120);
  ConvertFromReal(120.0);
  ConvertFromORDINAL(120);
  ConvertFromBv(120);
  ConvertFromUInt32(120);
  ConvertFromChar('x');
}

method ConvertFromInt(x: int)
  requires 0 <= x < 128
{
  print x as int, " ", x as real, " ", x as ORDINAL, " ", x as bv7, " ", x as uint32, " ", x as char, "\n";
}

method ConvertFromReal(x: real)
  requires x.Floor as real == x
  requires 0 <= x.Floor < 128
{
  print x as int, " ", x as real, " ", x as ORDINAL, " ", x as bv7, " ", x as uint32, " ", x as char, "\n";
}

method ConvertFromORDINAL(x: ORDINAL)
  requires 0 <= x < 128
{
  // ORDINAL doesn't (currently) support many type conversions
  print x as int, /** " ", x as real, " ", x as ORDINAL, " ", x as bv7,**/ " ", x as uint32, /** " ", x as char,**/ "\n";
}

method ConvertFromBv(x: bv7)
{
  print x as int, " ", x as real, " ", x as ORDINAL, " ", x as bv7, " ", x as uint32, " ", x as char, "\n";
}

method ConvertFromUInt32(x: uint32)
  requires 0 <= x < 128
{
  print x as int, " ", x as real, " ", x as ORDINAL, " ", x as bv7, " ", x as uint32, " ", x as char, "\n";
}

method ConvertFromChar(x: char)
  requires 0 as char <= x < 128 as char
{
  // char doesn't (currently) support many type conversions
  print x as int, /** " ", x as real, " ", x as ORDINAL, " ", x as bv7,**/ " ", x as uint32, /** " ", x as char,**/ "\n";
}

newtype MyInt = int

method ComparisonRegressions() {
  {
    var xx := 2_000_000_000_000_000_000_000;
    var yy := 3;
    print xx < yy, " ", yy < xx, " ", xx <= yy, " ", yy <= xx, "\n"; // false true false true
    print xx > yy, " ", yy > xx, " ", xx >= yy, " ", yy >= xx, "\n"; // true false true false
  }
  {
    var xx: MyInt := 2_000_000_000_000_000_000_000;
    var yy: MyInt := 3;
    // The following was once compiled incorrectly for JavaScript
    print xx < yy, " ", yy < xx, " ", xx <= yy, " ", yy <= xx, "\n"; // false true false true
    print xx > yy, " ", yy > xx, " ", xx >= yy, " ", yy >= xx, "\n"; // true false true false
  }
}

method CastRegressions() {
  var i: int := 20;
  var bt: uint8 := (i + 3) as uint8;
  var bu := (3 + i) as uint8;
  var b: bool;
  var bv: uint8 := if b then 89 else 88;
  var u: uint32 := if b then 890 else 880;
  print i, " ", bt, " ", bu, " ", bv, " ", u, "\n";
}
