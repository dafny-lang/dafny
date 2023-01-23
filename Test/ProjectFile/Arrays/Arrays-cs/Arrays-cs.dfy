// RUN: cd %s; %baredafny %args "%s" >> "%t"
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

  Index();
  More();
  MoreWithDefaults();

  Coercions();

  CharValues();

  TypeSynonym.Test();
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
newtype nLong = x | -10 <= x < 0x100_0000_0000_0000 witness 4
newtype ubyte = x | 0 <= x < 256

method Index() {
  var i: nByte := 0;
  var j: nLong := 1;
  var k: BV10 := 2;
  var l: ubyte := 250;  // we wanna be sure this does become negative when used in Java
  var m: int := 100;

  var a := new string[300];
  a[i] := "hi";
  a[j] := "hello";
  a[k] := "tjena";
  a[l] := "hej";
  a[m] := "hola";
  print a[i], " ", a[j], " ", a[k], " ", a[l], " ", a[m], "\n";

  var b := new string[20, 300];
  b[18, i] := "hi";
  b[18, j] := "hello";
  b[18, k] := "tjena";
  b[18, l] := "hej";
  b[18, m] := "hola";
  print b[18, i], " ", b[18, j], " ", b[18, k], " ", b[18, l], " ", b[18, m], "\n";

  var s := seq(300, _ => "x");
  s := s[i := "hi"];
  s := s[j := "hello"];
  s := s[k := "tjena"];
  s := s[l := "hej"];
  s := s[m := "hola"];
  print s[i], " ", s[j], " ", s[k], " ", s[l], " ", s[m], "\n";
}

method More() {
  var aa := new lowercase[3];
  forall i | 0 <= i < aa.Length {
    // aa[i] should not be '\0', but in case erroneous code causes it to get a zero-equivalent
    // value to be produced, then the following if-then-else will give better test output
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
  print kitchenSink, "\n";  // (d, 8, true, 1, 2, 3, 4)
}

type xchar = ch | '\0' <= ch <= 'z'
type xBV10 = x: bv10 | x != 999
type xYes = b | !b
newtype xnByte = x | -10 <= x < 100
newtype xnShort = x | -10 <= x < 1000
newtype xnInt = x | -10 <= x < 1_000_000
newtype xnLong = x | -10 <= x < 0x100_0000_0000_0000

method MoreWithDefaults() {
  var aa := new xchar[3];
  forall i | 0 <= i < aa.Length {
    aa[i] := if aa[i] == '\0' then 'a' else aa[i];  // don't print ugly '\0' characters into test output
  }
  PrintArray(aa);  // D D D

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

  var kitchenSink: (xchar, xBV10, xYes, xnByte, xnShort, xnInt, xnLong);
  if kitchenSink.0 == '\0' {
    kitchenSink := kitchenSink.(0 := 'a');  // don't print ugly '\0' characters into test output
  }
  print kitchenSink, "\n";  // (D, 0, false, 0, 0, 0, 0)
}

method Coercions() {
  // fields
  var cell := new Cell(8 as short);
  var a := cell.arr;
  var x := a[0];

  var b := new short[22];
  var y := b[0];

  print x, " ", y, "\n";  // 8 0

  // different types of arrays, where coercions may not be needed
  var c := new bool[22];
  var d := new int[22];
  var e := new object?[22];
  var f := new Cell?<real>[22];
  var c0, d0, e0, f0 := c[0], d[0], e[0], f[0];
  print c0, " ", d0, " ", e0, " ", f0, "\n";

  // function
  a := cell.FArray();
  // method with one out-parameter
  b := cell.MArray();
  x, y := a[0], b[0];
  print x, " ", y, "\n";
  // method with two out-parameters (which may need different compilation scheme)
  a, b := cell.MArray2();
  x, y := a[0], b[0];
  print x, " ", y, "\n";

  // lambda expression
  b := (sa => sa)(b);
  // array element
  var barray := new array<short>[9](_ => b);
  x, y := b[0], barray[3][0];
  print x, " ", y, "\n";

  // multi-dimensional arrays
  var marray := new array<short>[9, 2]((_, _) => b);
  x, y := marray[3, 1][0], cell.mat[7, 6];
  print x, " ", y, "\n";
}

newtype short = x | -10 <= x < 12_000

class Cell<T> {
  var arr: array<T>
  const crr: array<T>
  var mat: array2<T>
  constructor (t: T)
    ensures arr.Length == 15 && arr == crr
    ensures mat.Length0 == mat.Length1 == 15
  {
    arr := new T[15](_ => t);
    crr := arr;
    mat := new T[15, 15]((_, _) => t);
  }
  function method FArray(): array<T>
    reads this
  {
    arr
  }
  method MArray() returns (x: array<T>)
    ensures x == arr
  {
    x := arr;
  }
  method MArray2() returns (x: array<T>, y: array<T>)
    ensures x == y == arr
  {
    x, y := arr, arr;
  }
  method UArray(x: T)
    modifies arr
  {
    if arr.Length > 0 {
      arr[0] := x;
    }
  }
}

type ychar = ch | '\0' <= ch <= 'z'
type zchar = ch | '\0' <= ch <= 'z' witness 'r'

method CharValues() {
  var aa := new char[3];
  forall i | 0 <= i < aa.Length {
    aa[i] := if aa[i] == '\0' then 'a' else aa[i];  // don't print ugly '\0' characters into test output
  }
  PrintArray(aa);  // D D D

  var bb := new ychar[3];
  forall i | 0 <= i < bb.Length {
    bb[i] := if bb[i] == '\0' then 'a' else bb[i];  // don't print ugly '\0' characters into test output
  }
  PrintArray(bb);  // D D D

  var cc := new char[3];
  forall i | 0 <= i < cc.Length {
    cc[i] := if cc[i] == '\0' then 'a' else cc[i];  // don't print ugly '\0' characters into test output
  }
  PrintArray(cc);  // r r r

  var e0: char, e1: ychar, e2: zchar, ee: (char, ychar, zchar);
  print e0, " ", e1, " ", e2, " ", ee, "\n";  // D D r (D, D, r)

  var mm := new char[3, 3];
  var mx := new ychar[3, 3];
  var my := new zchar[3, 3];
  print mm[1, 2], " ", mx[1, 2], " ", my[1, 2], "\n";  // D D r
}

module TypeSynonym {
  export
    provides Test

  newtype uint8 = i:int | 0 <= i < 0x100

  type buffer<T> = a: array<T> | a.Length < 0x1_0000_0000 witness *
  type buffer_t = buffer<uint8>

  method BufferTest(b: buffer_t) {
    var t := b[..];
    print t, "\n";
  }

  method Test() {
    var b := new uint8[] [19, 18, 9, 8];
    BufferTest(b);
  }
}
