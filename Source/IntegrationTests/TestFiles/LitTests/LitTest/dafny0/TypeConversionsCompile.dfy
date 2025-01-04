// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --general-newtypes=false

// Note the difference in output in Java's case is due to
// https://github.com/dafny-lang/dafny/issues/4152

newtype Handful = x | 0 <= x < 0x8000  // this type turns native
newtype Abundance = y | -20 <= y < 0x200_0000_0000  // still fits inside a "long"
newtype int64 = y | -0x8000_0000_0000_0000 <= y < 0x8000_0000_0000_0000  // exactly a "long"
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

  //PrintExpected(x as bv67, 3); // disabled because it does not terminate with 4.4.2 Z3
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
  PrintExpected(seven as bv32, 127);
  PrintExpected(seven as bv67, 127);
  b67 := 50;
  //PrintExpected(b67 as bv32, 50); // disabled because it does not terminate with 4.4.2 Z3
  //PrintExpected(b67 as bv7, 50); // disabled because it does not terminate with 4.4.2 Z3
  PrintExpected(r as bv67, 5);
  PrintExpected(r as bv32, 5);
  PrintExpected(w as bv67, 0xFFFF_FFFF);
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
  Difficult();
  // here are some cases whose compilation are optimized
  var a0: Abundance, a1: Abundance, a2: Abundance, lng: int64;
  var s := {4.0, 6.3, r, 1000.2};
  var a := new char[68];
  handful := 120 as Handful;
  a0, a1 := -1 as Abundance, 4 as Abundance;
  a2 := 0x2_0000_0000 as Abundance;
  w, lng := 634_5789 as bv32, -0x8000_0000_0000_0000 as int64;
  print handful, " ", a0, " ", a1, " ", a2, " ", w, " ", lng, "\n";
  x, handful, a0, w := |s|, |s| as Handful, |s| as Abundance, |s| as bv32;
  print x, " ", handful, " ", a0, " ", w, "\n";
  x, handful, a0, w := a.Length, a.Length as Handful, a.Length as Abundance, a.Length as bv32;
  print x, " ", handful, " ", a0, " ", w, "\n";

  OrdinalTests();
}

method Difficult() {  // this has been made a separate method, because it was taking too long with /allocated:1
  if 14 as real as int as bv67 == 14 {  // help the verifier out, because Z3 doesn't know much about int/bv conversions
    PrintExpected(14 as real as int as bv67 as EvenInt as SmallReal as Handful as bv7 as bv32 as int, 14);  // take that!
  }
}

method OrdinalTests() {
  var ord: ORDINAL := 143;
  var iord := ord as int;
  var oord := iord as ORDINAL;
  print "Something about ORDINAL: ", ord, " ", iord, " ", oord, " ", ord + 4, " ", ord - 100, "\n";
  print "ORDINAL and bitvectors: ", 20 as bv32 as ORDINAL, " ", 20 as bv300 as ORDINAL, "\n";
  print ord.IsLimit, " ", ord.Offset, " ", ord.IsNat, "\n";
  ord := 0;
  print ord.IsLimit, " ", ord.Offset, " ", ord.IsNat, "\n";
}
