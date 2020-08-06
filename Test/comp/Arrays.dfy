// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method LinearSearch(a: array<int>, key: int) returns (n: nat)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == key
{
  n := 0;
  while n < a.Length
    invariant n <= a.Length
  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
}

method PrintArray<A>(a: array?<A>) {
  if (a == null) {
    print "It's null\n";
  } else {
    var i := 0;
    while i < a.Length {
      print a[i], " ";
      i := i + 1;
    }
    print "\n";
  }
}

method Main() {
  var a := new int[23];
  var i := 0;
  while i < 23 {
    a[i] := i;
    i := i + 1;
  }
  PrintArray(a);
  var n := LinearSearch(a, 17);
  print n, "\n";
  var s : seq<int> := a[..];
  print s, "\n";
  s := a[2..16];
  print s, "\n";
  s := a[20..];
  print s, "\n";
  s := a[..8];
  print s, "\n";

  // Conversion to sequence should copy elements (sequences are immutable!)
  a[0] := 42;
  print s, "\n";

  InitTests();

  MultipleDimensions();

  PrintArray<int>(null);

  More();
  MoreWithDefaults();
}

type lowercase = ch | 'a' <= ch <= 'z' witness 'd'

method InitTests() {
  var aa := new lowercase[3];
  PrintArray(aa);
  var s := "hello";
  aa := new lowercase[|s|](i requires 0 <= i < |s| => s[i]);
  PrintArray(aa);
}

method MultipleDimensions() {
  var matrix := new int[2,8];
  PrintMatrix(matrix);
  matrix := DiagMatrix(3, 5, 0, 1);
  PrintMatrix(matrix);

  var cube := new int[3,0,4]((_,_,_) => 16);
  print "cube dims: ", cube.Length0, " ", cube.Length1, " ", cube.Length2, "\n";

  var jagged := new array<int>[5];
  var i := 0;
  while i < 5 {
    jagged[i] := new int[i];
    i := i + 1;
  }
  PrintArrayArray(jagged);
}

method DiagMatrix<A>(rows: int, cols: int, zero: A, one: A)
    returns (a: array2<A>)
    requires rows >= 0 && cols >= 0
{
  return new A[rows, cols]((x,y) => if x==y then one else zero);
}

method PrintMatrix<A>(m: array2<A>) {
  var i := 0;
  while i < m.Length0 {
    var j := 0;
    while j < m.Length1 {
      print m[i,j], " ";
      j := j + 1;
    }
    print "\n";
    i := i + 1;
  }
}

method PrintArrayArray<A>(a: array<array<A>>) {
  var i := 0;
  while i < a.Length {
    print a[i][..], " ";
    i := i + 1;
  }
  print "\n";
}

type BV10 = x: bv10 | x != 999 witness 8
type Yes = b | b witness true
newtype nByte = x | -10 <= x < 100 witness 1
newtype nShort = x | -10 <= x < 1000 witness 2
newtype nInt = x | -10 <= x < 1_000_000 witness 3
newtype nLong = x | -10 <= x < 0x100_0000_0000 witness 4

method More() {
  var aa := new lowercase[3];
  forall i | 0 <= i < aa.Length {
    aa[i] := if aa[i] == '\0' then 'a' else aa[i];  // don't print ugly '\0' characters into test output
  }
  PrintArray(aa);

  var s := "hello";
  aa := new lowercase[|s|](i requires 0 <= i < |s| => s[i]);
  PrintArray(aa);

  var vv := new BV10[4];
  PrintArray(vv);

  var yy := new Yes[3];
  PrintArray(yy);

  var a0 := new nByte[5];
  PrintArray(a0);
  var a1 := new nShort[5];
  PrintArray(a1);
  var a2 := new nInt[5];
  PrintArray(a2);
  var a3 := new nLong[5];
  PrintArray(a3);

  var kitchenSink: (lowercase, BV10, Yes, nByte, nShort, nInt, nLong);
  if kitchenSink.0 == '\0' {
    kitchenSink := kitchenSink.(0 := 'a');  // don't print ugly '\0' characters into test output
  }
  print kitchenSink, "\n";
}

type xlowercase = ch | '\0' <= ch <= 'z' && ch != 'D'
type xBV10 = x: bv10 | x != 999
type xYes = b | !b
newtype xnByte = x | -10 <= x < 100
newtype xnShort = x | -10 <= x < 1000
newtype xnInt = x | -10 <= x < 1_000_000
newtype xnLong = x | -10 <= x < 0x100_0000_0000

method MoreWithDefaults() {
  var aa := new xlowercase[3];
  forall i | 0 <= i < aa.Length {
    aa[i] := if aa[i] == '\0' then 'a' else aa[i];  // don't print ugly '\0' characters into test output
  }
  PrintArray(aa);

  var vv := new xBV10[4];
  PrintArray(vv);

  var yy := new xYes[3];
  PrintArray(yy);

  var a0 := new xnByte[5];
  PrintArray(a0);
  var a1 := new xnShort[5];
  PrintArray(a1);
  var a2 := new xnInt[5];
  PrintArray(a2);
  var a3 := new xnLong[5];
  PrintArray(a3);

  var kitchenSink: (xlowercase, xBV10, xYes, xnByte, xnShort, xnInt, xnLong);
  if kitchenSink.0 == '\0' {
    kitchenSink := kitchenSink.(0 := 'a');  // don't print ugly '\0' characters into test output
  }
  print kitchenSink, "\n";
}
