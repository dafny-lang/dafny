// RUN: %baredafny verify %args --relax-definite-assignment "%s" > "%t"
// RUN: %baredafny run --unicode-char:false --no-verify --target=cs %args "%s" >> "%t"
// RUN: %baredafny run --unicode-char:false --no-verify --target=js %args  "%s" >> "%t"
// RUN: %baredafny run --unicode-char:false --no-verify --target=go %args  "%s" >> "%t"
// RUN: %baredafny run --unicode-char:false --no-verify --target=java %args  "%s" >> "%t"
// RUN: %baredafny run --unicode-char:false --no-verify --target=py %args  "%s" >> "%t"
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

  MoreArrays.Test();
  NativeArrays.Test();
  SimultaneousAssignment.Test();
  ArrayToSeq.Test();

  ArrayAllocationInitialization.Test();
  VariationsOnIndexAndDimensionTypes.Test();
  TypeSpecialization.Test();

  GenericArrayEquality.Test();
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
  function FArray(): array<T>
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

module MoreArrays {
  newtype byte = x | 0 <= x < 256

  class MyClass { }

  method Test() {
    TestEqualityOfSomeNonArraysToo();

    var a := StringToByteArray("hello there");
    WriteLine(a);

    var b := StringToByteArray("hello there");
    print a == b; // false
    CheckEquality(a, b); // false (this once caused the emitted JavaScript to crash, see issue #3207)
    print a == a; // true
    CheckEquality(a, a); // true
    var c: array?<byte> := null;
    print a == c; // false
    CheckEquality(a, c); // false
    print c == a; // false
    CheckEquality(c, a); // false
  }

  method TestEqualityOfSomeNonArraysToo() {
    var bb: byte := 76;
    CheckEquality(bb, bb); // true
    CheckEquality(bb, bb + 1); // false

    var cc0 := new MyClass;
    var cc1 := new MyClass;
    CheckEquality(cc0, cc0); // true
    CheckEquality(cc0, cc1); // false
    CheckEquality(cc0, null); // false
    CheckEquality(null, cc0); // false
    CheckEquality(null, null); // true

    var s0 := [20, 10, 20];
    var s1 := [20, 10, 20];
    var s2 := [20, 10, 22];
    CheckEquality(s0, s1); // true
    CheckEquality(s0, s2); // false

    CheckEquality((true, 100), (true, 100)); // true
    CheckEquality((true, 100), (false, 100)); // false

    var m0 := map[4 := true, 3 := false];
    var m1 := map[4 := true][3 := false];
    var m2 := map[3 := false][4 := true][3 := false][4 := true];
    var m3 := map[3 := false][4 := false][3 := false][3 := false];
    CheckEquality(m0, m1); // true
    CheckEquality(m0, m2); // true
    CheckEquality(m0, m3); // false
  }

  method StringToByteArray(s: string) returns (arr: array<byte>) {
    arr := new [|s|];
    forall i | 0 <= i < |s| {
      arr[i] := (var ch := s[i]; if ' ' <= ch <= 'z' then ch else 'X') as byte;
    }
  }

  method WriteLine(arr: array<byte>) {
    for i := 0 to arr.Length {
      print [arr[i] as char];
    }
    print "\n";
  }

  method CheckEquality<T(==)>(x: T, y: T) {
    print " ", x == y, "\n";
  }
}

module NativeArrays {
  newtype byte = x | 0 <= x < 256
  newtype onebyte = x | 0 < x < 256 witness 1

  method Test() {
    var aa := new byte[3];
    PrintArray(aa, "uninitialized bytes");
    aa := new byte[] [7, 8, 9];
    PrintArray(aa, "bytes from display");
    aa := new byte[3](i => if 0 <= i < 10 then (20 + i) as byte else 88);
    PrintArray(aa, "bytes from lambda");

    var bb := new onebyte[3];
    PrintArray(bb, "uninitialized 1bytes");
    bb := new onebyte[] [7, 8, 9];
    PrintArray(bb, "1bytes from display");
    bb := new onebyte[3](i => if 0 <= i < 10 then (20 + i) as onebyte else 88);
    PrintArray(bb, "1bytes from lambda");

    TestVariousFlavorsOfIndices();
  }

  method PrintArray(a: array, title: string) {
    print title, ": array[";
    for i := 0 to a.Length {
      print if i == 0 then "" else ", ", a[i];
    }
    print "]\n";
  }

  method TestVariousFlavorsOfIndices() {
    var arr := new int[250];
    var m := new int[20, 30];

    arr[3 as bv19] := 17;
    arr[4 as bv5] := 19;
    var iIndex: int, bIndex: byte, bvIndex: bv9 := 3, 4, 5;
    m[iIndex, bIndex] := arr[iIndex];
    arr[iIndex] := m[iIndex, bvIndex - 1];
    assert arr[iIndex] == 17;
    print arr[iIndex], " "; // 17
    m[bIndex, iIndex] := arr[bIndex];
    arr[bIndex] := m[bvIndex - 1, iIndex];
    assert arr[bIndex] == 19;
    print arr[bIndex], " "; // 19
    m[iIndex, iIndex] := arr[iIndex] + 1;
    arr[iIndex] := m[iIndex, iIndex];
    m[bIndex, bIndex] := arr[bIndex] + 1;
    arr[bIndex] := m[bIndex, bIndex];
    print arr[iIndex], " ", arr[bIndex], "\n"; // 18 20
  }
}

module SimultaneousAssignment {
  method Test() {
    var arr := new int[250];
    var m := new int[20, 30];
    var arr', m' := arr, m;

    var a, b, c := 18, 28, 38;
    var arr'' := new int[1];
    var m'' := new int[1, 1];

    arr, a, arr[a + b], m, arr, c, m[a, b], b, m := arr'', 100, 120, m'', arr'', 300, c, 200, m'';

    print a, " ", b, " ", c, " ", arr'[46], " ", m'[18, 28], "\n"; // 100 120 200 300 38
  }
}

module ArrayToSeq {
  newtype byte = x | 0 <= x < 256

  trait TraitMeRite {
  }

  class MyClass extends TraitMeRite {
  }

  method Test() {
    var arrChar := new [] ['h', 'e', 'l', 'l', 'o'];
    var arrInt := new int[5](i => i);
    var arrByte := new byte[5](_ => 2);
    var c: MyClass := new MyClass;
    var tr: TraitMeRite := c;
    var arrClass := new MyClass[] [c, c, c];
    var arrTrait := new TraitMeRite[] [tr, c, tr];

    var s0 := arrChar[..];
    var s1 := arrInt[..];
    var s2 := arrByte[..];
    var s3 := arrClass[..];
    var s4 := arrTrait[..];

    expect s0 == "hello";
    expect arrInt[1..][..2] == arrInt[..3][1..];
    expect arrInt[1 as byte..][..2] == arrInt[..3 as byte][1..];
    expect arrInt[1 as byte..3] == arrInt[1..3 as byte];
    expect arrByte[..0] <= arrByte[5..] <= arrByte[..3] <= s2;
    expect s3 == s4;

    print s0, " ";
    print s1, " ";
    print s2, "\n";
  }
}

module {:options "/functionSyntax:4"} ArrayAllocationInitialization {
  newtype AutoInit = x | 20 <= x < 2_000_000 witness 77
  newtype NonAutoInit = x | 20 <= x < 2_000_000 witness *
  newtype byte = x | 0 <= x < 256

  function AutoInitF(i: nat): AutoInit { if 20 <= i < 30 then i as AutoInit else 78 }
  function NonAutoInitF(i: nat): NonAutoInit { 82 }
  function ByteF(i: nat): byte { if 20 <= i < 30 then i as byte else 60 }
  function CharF(i: nat): char { if 20 <= i < 30 then 'a' + (i - 20) as char else 'g' }

  function AutoInitF2(i: nat, j: nat): AutoInit { if i == j then 50 else 78 }
  function ByteF2(i: nat, j: nat): byte { if i == j then 50 else 60 }
  function CharF2(i: nat, j: nat): char { if i == j then 'a' else 'g' }

  method Test() {
    TestAutoInit();
    TestTypeParameter(AutoInitF);

    TestNonAutoInit();

    TestByte();
    TestTypeParameter(ByteF);

    TestChar();
    TestTypeParameter(CharF);

    TestMatrixAutoInit();
    TestMatrixTypeParameter(AutoInitF2);
    TestMatrixTypeParameter(ByteF2);
    TestMatrixTypeParameter(CharF2);
  }

  method TestAutoInit() {
    var zero, five := 0, 5;
    var a: array<AutoInit>;
    var s := [];

    a := new AutoInit[zero];
    s := s + a[..];
    a := new AutoInit[five]; // initialized by the default element
    s := s + a[..];
    a := new AutoInit[zero] []; // initialized as given (no elements)
    s := s + a[..];
    a := new AutoInit[] []; // initialized as given (no elements)
    s := s + a[..];
    a := new AutoInit[five] [20, 21, 22, 23, 24]; // initialized as given (5 elements)
    s := s + a[..];
    a := new AutoInit[] [20, 21, 22, 23, 24]; // initialized as given (5 elements)
    s := s + a[..];
    a := new AutoInit[zero](AutoInitF);
    s := s + a[..];
    a := new AutoInit[five](AutoInitF);
    s := s + a[..];

    print s, "\n";
  }

  method TestNonAutoInit() {
    var zero, five := 0, 5;
    var a: array<NonAutoInit>;
    var s := [];

    a := new NonAutoInit[zero];
    s := s + a[..];
    // Note, "new NonAutoInit[five]" is not allowed for a non-auto-init type
    s := s + [99, 99, 99, 99, 99];
    a := new NonAutoInit[zero] []; // initialized as given (no elements)
    s := s + a[..];
    a := new NonAutoInit[] []; // initialized as given (no elements)
    s := s + a[..];
    a := new NonAutoInit[five] [20, 21, 22, 23, 24]; // initialized as given (5 elements)
    s := s + a[..];
    a := new NonAutoInit[] [20, 21, 22, 23, 24]; // initialized as given (5 elements)
    s := s + a[..];
    a := new NonAutoInit[zero](NonAutoInitF);
    s := s + a[..];
    a := new NonAutoInit[five](NonAutoInitF);
    s := s + a[..];

    print s, "\n";
  }

  method TestByte() {
    var zero, five := 0, 5;
    var a: array<byte>;
    var s := [];

    a := new byte[zero];
    s := s + a[..];
    a := new byte[five]; // initialized by the default element
    s := s + a[..];
    a := new byte[zero] []; // initialized as given (no elements)
    s := s + a[..];
    a := new byte[] []; // initialized as given (no elements)
    s := s + a[..];
    a := new byte[five] [20, 21, 22, 23, 24]; // initialized as given (5 elements)
    s := s + a[..];
    a := new byte[] [20, 21, 22, 23, 24]; // initialized as given (5 elements)
    s := s + a[..];
    a := new byte[zero](ByteF);
    s := s + a[..];
    a := new byte[five](ByteF);
    s := s + a[..];

    print s, "\n";
  }

  method TestChar() {
    var zero, five := 0, 5;
    var a: array<char>;
    var s := [];

    a := new char[zero];
    s := s + a[..];
    a := new char[five]; // initialized by the default element
    s := s + a[..];
    a := new char[zero] []; // initialized as given (no elements)
    s := s + a[..];
    a := new char[] []; // initialized as given (no elements)
    s := s + a[..];
    a := new char[five] ['a', 'b', 'c', 'd', 'e']; // initialized as given (5 elements)
    s := s + a[..];
    a := new char[] ['a', 'b', 'c', 'd', 'e']; // initialized as given (5 elements)
    s := s + a[..];
    a := new char[zero](CharF);
    s := s + a[..];
    a := new char[five](CharF);
    s := s + a[..];

    print s, "\n";
  }

  method TestTypeParameter<T(0)>(initF: nat -> T) {
    var zero, five := 0, 5;
    var a: array<T>;
    var s := [];

    a := new T[zero];
    s := s + a[..];
    a := new T[five]; // initialized by the default element
    s := s + a[..];
    a := new T[zero] []; // initialized as given (no elements)
    s := s + a[..];
    a := new T[] []; // initialized as given (no elements)
    s := s + a[..];
    a := new T[five] [initF(20), initF(21), initF(22), initF(23), initF(24)]; // initialized as given (5 elements)
    s := s + a[..];
    a := new T[] [initF(20), initF(21), initF(22), initF(23), initF(24)]; // initialized as given (5 elements)
    s := s + a[..];
    a := new T[zero](initF);
    s := s + a[..];
    a := new T[five](initF);
    s := s + a[..];

    print s, "\n";
  }

  function MatrixToSequence<T>(m: array2<T>): seq<T>
    reads m
  {
    M2S(m, 0, 0)
  }

  function M2S<T>(m: array2<T>, i: nat, j: nat): seq<T>
    requires i <= m.Length0 && j <= m.Length1
    requires i == m.Length0 ==> j == 0
    reads m
    decreases m.Length0 - i, m.Length1 - j
  {
    if i == m.Length0 then
      []
    else if j == m.Length1 then
      M2S(m, i + 1, 0)
    else
      [m[i, j]] + M2S(m, i, j + 1)
  }

  method TestMatrixAutoInit() {
    var zero, two, five := 0, 2, 5;
    var a: array2<AutoInit>;
    var s := [];

    a := new AutoInit[zero, zero];
    s := s + MatrixToSequence(a);
    a := new AutoInit[zero, five];
    s := s + MatrixToSequence(a);
    a := new AutoInit[five, zero];
    s := s + MatrixToSequence(a);
    a := new AutoInit[two, five]; // initialized by the default element
    s := s + MatrixToSequence(a);
    
    a := new AutoInit[zero, zero](AutoInitF2);
    s := s + MatrixToSequence(a);
    a := new AutoInit[zero, five](AutoInitF2);
    s := s + MatrixToSequence(a);
    a := new AutoInit[five, zero](AutoInitF2);
    s := s + MatrixToSequence(a);
    a := new AutoInit[two, five](AutoInitF2);
    s := s + MatrixToSequence(a);

    print s, "\n";
  }

  method TestMatrixTypeParameter<T(0)>(initF2: (nat, nat) -> T) {
    var zero, two, five := 0, 2, 5;
    var a: array2<T>;
    var s := [];

    a := new T[zero, zero];
    s := s + MatrixToSequence(a);
    a := new T[zero, five];
    s := s + MatrixToSequence(a);
    a := new T[five, zero];
    s := s + MatrixToSequence(a);
    a := new T[two, five]; // initialized by the default element
    s := s + MatrixToSequence(a);

    a := new T[zero, zero](initF2);
    s := s + MatrixToSequence(a);
    a := new T[zero, five](initF2);
    s := s + MatrixToSequence(a);
    a := new T[five, zero](initF2);
    s := s + MatrixToSequence(a);
    a := new T[two, five](initF2);
    s := s + MatrixToSequence(a);

    print s, "\n";
  }
}

module {:options "/functionSyntax:4"} VariationsOnIndexAndDimensionTypes {
  newtype byte = x | 0 <= x < 256
  newtype onebyte = x | 0 < x < 256 witness 1
  newtype Long = x | -0x8000_0000_0000_0000 < x < 0x8000_0000_0000_0000

  method Test() {
    TestArray();
    TestMatrix();
  }

  method TestArray() {
    var aa;
    aa := new byte[3](i => if 0 <= i < 10 then (20 + i) as byte else 88);
  }

  method TestMatrix() {
    var a, b, c := 3 as byte, 2, 5 as Long;
    var m := new byte[a, b, c](F);
    expect m[0 as byte, 1, 2 as Long]
         + m[1 as Long, 1 as byte, 2]
         + m[2, 1 as Long, 2 as byte]
        == 138;
  }

  function F(a: nat, b: nat, c: nat): byte {
    if a == 0 then
      45
    else if a == 1 then
      46
    else
      47
  }
}

module TypeSpecialization {
  newtype byte = x | 0 <= x < 256

  method Test() {
    var a := new int[100];
    Int(a, a, 50);
    print a[19], " ", a[20], " ", a[21], "\n";

    var b := new byte[100];
    Byte(b, b, 50);
    print b[19], " ", b[20], " ", b[21], "\n";

    var c := new char[100];
    Char(c, c, 'n');
    print c[19], " ", c[20], " ", c[21], "\n";
  }

  method Int<T>(a: array<T>, b: array<int>, t: T)
    requires a.Length == b.Length == 100
    modifies a, b
  {
    a[20] := t;
    b[20] := 69;
    b[21] := 69;
    a[21] := t;
  }

  method Byte<T>(a: array<T>, b: array<byte>, t: T)
    requires a.Length == b.Length == 100
    modifies a, b
  {
    a[20] := t;
    b[20] := 69;
    b[21] := 69;
    a[21] := t;
  }

  method Char<T>(a: array<T>, b: array<char>, t: T)
    requires a.Length == b.Length == 100
    modifies a, b
  {
    a[20] := t;
    b[20] := 'k';
    b[21] := 'k';
    a[21] := t;
  }
}

module GenericArrayEquality {
  method Test() {
    var a := new int[25];
    var b := new int[25];
    ArrayCompare(a, b); // false
    GenericCompare(a, b); // false

    // In Go, an array is stored as a struct that contains a pointer to the actual array elements.
    // An easy mistake (in the runtime) would be to compare the address of the struct to determine
    // array equality. The following test checks that it's done properly.
    b := a;
    ArrayCompare(a, b); // true
    GenericCompare(a, b); // true

    b := null;
    ArrayCompare(a, b); // false
    GenericCompare(a, b); // false
    ArrayCompare(b, a); // false
    GenericCompare(b, a); // false

    a := null;
    ArrayCompare(a, b); // true
    GenericCompare(a, b); // true
  }

  method ArrayCompare<X>(a: array?<X>, b: array?<X>) {
    print a == b, " ";
  }
  

  method GenericCompare<X(==)>(a: X, b: X) {
    print a == b, "\n";
  }
}
