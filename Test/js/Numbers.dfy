// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Print(description: string, x: int) {
  print x;
  if |description| != 0 {  // string length (that is, sequence length)
    print " (aka ", description, ")";
  }
  print "\n";
}

method PrintReal(description: string, x: real) {
  print x;
  if |description| != 0 {
  // TODO:  if description != "" {  // string comparison
    print " (aka ", description, ")";
  }
  print "\n";
}

method Main() {
  Literals();
  Arithmetic();
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
  print 31 + 4, " ", 31 - 4, " ", 4 - 31, "\n";

  print 31 * 4, " ", 31 * -4, "\n";
  print -31 * 4, " ", -31 * -4, "\n";

  DivMod(31, 4);
  DivMod(-31, 4);
  DivMod(31, -4);
  DivMod(-31, -4);
  DivMod(0, 4);
  DivMod(0, -4);

  print 0.3 - 0.1, "\n";  // should be 0.2, not something like 0.19999999999999998
  print 31.2 + 4.0, " ", 31.2 - 4.0, " ", 4.0 - 31.2, "\n";

  print 31.2 * 4.0, " ", 31.2 * -4.0, "\n";
  print -31.2 * 4.0, " ", -31.2 * -4.0, "\n";

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
