// RUN: %dafny /compile:3 /print:"%t.print" /env:0 /rprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Handful = x | 0 <= x < 0x8000  // this type turns native
newtype EvenInt = x | x % 2 == 0
newtype SmallReal = r | -4.0 <= r < 300.0

method Print(x: int, n: nat, r: real, handful: Handful, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0)
{
  print x, " ", n, " ", r, " ", handful, " ", even, " ", small, " ", b67, " ", w, " ", seven, " ", noll, "\n";
}

method PrintExpected<T>(got: T, expected: T) {
  print "got ", got, ", expected ", expected, "\n";
}

method Main()
{
  var x: int, n: nat, r: real := 3, 4, 5.0;
  var handful: Handful, even: EvenInt, small: SmallReal := 5, 6, -1.0;
  var b67: bv67, w: bv32, seven: bv7, noll: bv0 := 0x7_FFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF, 127, 0;
  Print(x, n, r, handful, even, small, b67, w, seven, noll);

  PrintExpected(x as bv67, 3);
  PrintExpected(x as bv7, 3);
  PrintExpected(0 as bv0, 0);
  PrintExpected(r as int, 5);
  PrintExpected((2.0*r) as EvenInt, 10);
  PrintExpected(x as real, 3.0);
  PrintExpected(even as real, 6.0);
  PrintExpected((small + 3.0) as Handful, 2);
  PrintExpected(noll as Handful, 0);
  PrintExpected(noll as SmallReal, 0.0);
  PrintExpected(w as real, 4294967295.0);
  PrintExpected(seven as real, 127.0);
  PrintExpected(noll as bv32, 0);
  PrintExpected(noll as bv67, 0);
  PrintExpected(seven as bv32, 127);  // TODO: strange type inference error
  PrintExpected(seven as bv67, 127);  // TODO: strange type inference error
  b67 := 50;
  PrintExpected(b67 as bv32, 50);
  PrintExpected(b67 as bv7, 50);
  PrintExpected(r as bv67, 5);
  PrintExpected(r as bv32, 5);
  PrintExpected(w as bv67, 0xFFFF_FFFF);  // TODO: strange type inference error
  PrintExpected(r as bv7, 5);
  PrintExpected(0.0 as bv0, 0);
  PrintExpected(handful as bv67, 5);
  PrintExpected(handful as bv32, 5);
  PrintExpected(handful as bv7, 5);
  PrintExpected(handful as int, 5);
  PrintExpected(noll as bv32 as bv0, 0);
  PrintExpected(noll as bv67 as bv0, 0);
  PrintExpected(seven as bv32 as bv7, 127);
  PrintExpected(seven as bv67 as bv7, 127);
  PrintExpected(handful as real, 5.0);
  if 14 as real as int as bv67 == 14 {  // help the verifier out, because Z3 doesn't know much about int/bv conversions
    PrintExpected(14 as real as int as bv67 as EvenInt as SmallReal as Handful as bv7 as bv32 as int, 14);  // take that!
  }
}
