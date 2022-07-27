// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Some runtimes (like the one for C#) have three implementations
// of Euclidean div/mod: one for `int`, one for `long`, and one
// for `BigInteger`.

const TWO_15: int := 0x0_8000
const TWO_63: int := 0x0_8000_0000_0000_0000
const TWO_127: int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000

// I0, I1, I2, and I3 use the BigInteger versions
type I0 = int
newtype I1 = int
newtype I2 = x: int | true
newtype I3 = x | -TWO_127 <= x < TWO_127
// I4 uses the int version
newtype I4 = x | -TWO_15 <= x < TWO_15
// I5 uses the long version
newtype I5 = x | -TWO_63 <= x < TWO_63

method M0() {
  var neg: I0, pos: I0;
  neg, pos := -6, 6;

  // div

  var a := neg / (-4); assert a == 2;
  var b := pos / (-4); assert b == -1;
  var c := neg / ( 4); assert c == -2;
  var d := pos / ( 4); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-4) / (-2); assert a == 2;
  b := ( 4) / (-2); assert b == -2;
  c := (-4) / ( 2); assert c == -2;
  d := ( 4) / ( 2); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := 101 / (-3); assert a == -33;
  b := 100 / (-3); assert b == -33;
  c :=  99 / (-3); assert c == -33;
  d :=  98 / (-3); assert d == -32;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) / 3; assert a == -34;
  b := (-100) / 3; assert b == -34;
  c := ( -99) / 3; assert c == -33;
  d := ( -98) / 3; assert d == -33;
  print a, " ", b, " ", c, " ", d, "   ";

  // mod

  a := (-101) % (-3); assert a == 1;
  b := (-100) % (-3); assert b == 2;
  c := ( -99) % (-3); assert c == 0;
  d := ( -98) % (-3); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := ( 101) % (-3); assert a == 2;
  b := ( 100) % (-3); assert b == 1;
  c := (  99) % (-3); assert c == 0;
  d := (  98) % (-3); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) % 3; assert a == 1;
  b := (-100) % 3; assert b == 2;
  c := ( -99) % 3; assert c == 0;
  d := ( -98) % 3; assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (101) % 3; assert a == 2;
  b := (100) % 3; assert b == 1;
  c := ( 99) % 3; assert c == 0;
  d := ( 98) % 3; assert d == 2;
  print a, " ", b, " ", c, " ", d, "\n";
}

method M1() {
  var neg: I1, pos: I1;
  neg, pos := -6, 6;

  // div

  var a := neg / (-4); assert a == 2;
  var b := pos / (-4); assert b == -1;
  var c := neg / ( 4); assert c == -2;
  var d := pos / ( 4); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-4) / (-2); assert a == 2;
  b := ( 4) / (-2); assert b == -2;
  c := (-4) / ( 2); assert c == -2;
  d := ( 4) / ( 2); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := 101 / (-3); assert a == -33;
  b := 100 / (-3); assert b == -33;
  c :=  99 / (-3); assert c == -33;
  d :=  98 / (-3); assert d == -32;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) / 3; assert a == -34;
  b := (-100) / 3; assert b == -34;
  c := ( -99) / 3; assert c == -33;
  d := ( -98) / 3; assert d == -33;
  print a, " ", b, " ", c, " ", d, "   ";

  // mod

  a := (-101) % (-3); assert a == 1;
  b := (-100) % (-3); assert b == 2;
  c := ( -99) % (-3); assert c == 0;
  d := ( -98) % (-3); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := ( 101) % (-3); assert a == 2;
  b := ( 100) % (-3); assert b == 1;
  c := (  99) % (-3); assert c == 0;
  d := (  98) % (-3); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) % 3; assert a == 1;
  b := (-100) % 3; assert b == 2;
  c := ( -99) % 3; assert c == 0;
  d := ( -98) % 3; assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (101) % 3; assert a == 2;
  b := (100) % 3; assert b == 1;
  c := ( 99) % 3; assert c == 0;
  d := ( 98) % 3; assert d == 2;
  print a, " ", b, " ", c, " ", d, "\n";
}

method M2() {
  var neg: I2, pos: I2;
  neg, pos := -6, 6;

  // div

  var a := neg / (-4); assert a == 2;
  var b := pos / (-4); assert b == -1;
  var c := neg / ( 4); assert c == -2;
  var d := pos / ( 4); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-4) / (-2); assert a == 2;
  b := ( 4) / (-2); assert b == -2;
  c := (-4) / ( 2); assert c == -2;
  d := ( 4) / ( 2); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := 101 / (-3); assert a == -33;
  b := 100 / (-3); assert b == -33;
  c :=  99 / (-3); assert c == -33;
  d :=  98 / (-3); assert d == -32;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) / 3; assert a == -34;
  b := (-100) / 3; assert b == -34;
  c := ( -99) / 3; assert c == -33;
  d := ( -98) / 3; assert d == -33;
  print a, " ", b, " ", c, " ", d, "   ";

  // mod

  a := (-101) % (-3); assert a == 1;
  b := (-100) % (-3); assert b == 2;
  c := ( -99) % (-3); assert c == 0;
  d := ( -98) % (-3); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := ( 101) % (-3); assert a == 2;
  b := ( 100) % (-3); assert b == 1;
  c := (  99) % (-3); assert c == 0;
  d := (  98) % (-3); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) % 3; assert a == 1;
  b := (-100) % 3; assert b == 2;
  c := ( -99) % 3; assert c == 0;
  d := ( -98) % 3; assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (101) % 3; assert a == 2;
  b := (100) % 3; assert b == 1;
  c := ( 99) % 3; assert c == 0;
  d := ( 98) % 3; assert d == 2;
  print a, " ", b, " ", c, " ", d, "\n";
}

method M3() {
  var neg: I3, pos: I3;
  neg, pos := -6, 6;

  // div

  var a := neg / (-4); assert a == 2;
  var b := pos / (-4); assert b == -1;
  var c := neg / ( 4); assert c == -2;
  var d := pos / ( 4); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-4) / (-2); assert a == 2;
  b := ( 4) / (-2); assert b == -2;
  c := (-4) / ( 2); assert c == -2;
  d := ( 4) / ( 2); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := 101 / (-3); assert a == -33;
  b := 100 / (-3); assert b == -33;
  c :=  99 / (-3); assert c == -33;
  d :=  98 / (-3); assert d == -32;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) / 3; assert a == -34;
  b := (-100) / 3; assert b == -34;
  c := ( -99) / 3; assert c == -33;
  d := ( -98) / 3; assert d == -33;
  print a, " ", b, " ", c, " ", d, "   ";

  // mod

  a := (-101) % (-3); assert a == 1;
  b := (-100) % (-3); assert b == 2;
  c := ( -99) % (-3); assert c == 0;
  d := ( -98) % (-3); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := ( 101) % (-3); assert a == 2;
  b := ( 100) % (-3); assert b == 1;
  c := (  99) % (-3); assert c == 0;
  d := (  98) % (-3); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) % 3; assert a == 1;
  b := (-100) % 3; assert b == 2;
  c := ( -99) % 3; assert c == 0;
  d := ( -98) % 3; assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (101) % 3; assert a == 2;
  b := (100) % 3; assert b == 1;
  c := ( 99) % 3; assert c == 0;
  d := ( 98) % 3; assert d == 2;
  print a, " ", b, " ", c, " ", d, "\n";
}

method M4() {
  var neg: I4, pos: I4;
  neg, pos := -6, 6;

  // div

  var a := neg / (-4); assert a == 2;
  var b := pos / (-4); assert b == -1;
  var c := neg / ( 4); assert c == -2;
  var d := pos / ( 4); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-4) / (-2); assert a == 2;
  b := ( 4) / (-2); assert b == -2;
  c := (-4) / ( 2); assert c == -2;
  d := ( 4) / ( 2); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := 101 / (-3); assert a == -33;
  b := 100 / (-3); assert b == -33;
  c :=  99 / (-3); assert c == -33;
  d :=  98 / (-3); assert d == -32;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) / 3; assert a == -34;
  b := (-100) / 3; assert b == -34;
  c := ( -99) / 3; assert c == -33;
  d := ( -98) / 3; assert d == -33;
  print a, " ", b, " ", c, " ", d, "   ";

  // mod

  a := (-101) % (-3); assert a == 1;
  b := (-100) % (-3); assert b == 2;
  c := ( -99) % (-3); assert c == 0;
  d := ( -98) % (-3); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := ( 101) % (-3); assert a == 2;
  b := ( 100) % (-3); assert b == 1;
  c := (  99) % (-3); assert c == 0;
  d := (  98) % (-3); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) % 3; assert a == 1;
  b := (-100) % 3; assert b == 2;
  c := ( -99) % 3; assert c == 0;
  d := ( -98) % 3; assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (101) % 3; assert a == 2;
  b := (100) % 3; assert b == 1;
  c := ( 99) % 3; assert c == 0;
  d := ( 98) % 3; assert d == 2;
  print a, " ", b, " ", c, " ", d, "\n";
}

method M5() {
  var neg: I5, pos: I5;
  neg, pos := -6, 6;

  // div

  var a := neg / (-4); assert a == 2;
  var b := pos / (-4); assert b == -1;
  var c := neg / ( 4); assert c == -2;
  var d := pos / ( 4); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-4) / (-2); assert a == 2;
  b := ( 4) / (-2); assert b == -2;
  c := (-4) / ( 2); assert c == -2;
  d := ( 4) / ( 2); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := 101 / (-3); assert a == -33;
  b := 100 / (-3); assert b == -33;
  c :=  99 / (-3); assert c == -33;
  d :=  98 / (-3); assert d == -32;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) / 3; assert a == -34;
  b := (-100) / 3; assert b == -34;
  c := ( -99) / 3; assert c == -33;
  d := ( -98) / 3; assert d == -33;
  print a, " ", b, " ", c, " ", d, "   ";

  // mod

  a := (-101) % (-3); assert a == 1;
  b := (-100) % (-3); assert b == 2;
  c := ( -99) % (-3); assert c == 0;
  d := ( -98) % (-3); assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := ( 101) % (-3); assert a == 2;
  b := ( 100) % (-3); assert b == 1;
  c := (  99) % (-3); assert c == 0;
  d := (  98) % (-3); assert d == 2;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (-101) % 3; assert a == 1;
  b := (-100) % 3; assert b == 2;
  c := ( -99) % 3; assert c == 0;
  d := ( -98) % 3; assert d == 1;
  print a, " ", b, " ", c, " ", d, "   ";

  a := (101) % 3; assert a == 2;
  b := (100) % 3; assert b == 1;
  c := ( 99) % 3; assert c == 0;
  d := ( 98) % 3; assert d == 2;
  print a, " ", b, " ", c, " ", d, "\n";
}

method Main() {
  // This is expected to print six lines of:
  // 2 -1 -2 1   2 -2 -2 2   -33 -33 -33 -32   -34 -34 -33 -33   1 2 0 1   2 1 0 2   1 2 0 1   2 1 0 2
  M0();
  M1();
  M2();
  M3();
  M4();
  M5();
}
