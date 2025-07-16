// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --type-system-refresh=true --general-newtypes=true

method Main() {
  Numerics.Test();
  SimpleBoolAndint.Test();
  TrivialConstraint.Test();
  BaseTypesThatAreSubsetTypes.Test();
  TypeDescriptors.Test();
  PrintChars.Test();
  Bitvectors.Test();
  SubsetTypeIsTests.Test();
  NewtypeIsTests.Test();
  NewBehaviors.Test();
  TypeParameters.Test();
  AutoInit.Test();
  RefinementB.Test(2.0, 3.0);
  SimpleNewtypeWitness.Test();
  CharToInt.Test();
}

module Numerics {
  newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  newtype j32 = i32

  newtype k32 = j: j32 | true

  newtype nn = x: int | 0 <= x
  newtype byte = n: nn | n < 256

  method Test() {
    var i: i32 := 100;
    var j: j32 := 100;

    print i, " ", j, "\n"; // 100 100
    print i == i, " ", j == j, "\n"; // true true
    print i == j as i32, " ", i as j32 == j, "\n"; // true true
    print i as int == j as int, "\n"; // true

    var k: k32 := 99;
    var n: nn := 99;
    var b: byte := 99;

    print k, " ", n, " ", b, "\n"; // 99 99
    print k == k, " ", n == n, " ", b == b, "\n"; // true true true
    print k == n as k32, " ", n == b as nn, " ", b == k as byte, "\n"; // true true true
  }
}

module SimpleBoolAndint {
  export
    provides Test

  newtype MyBool = bool
  newtype MyInt = int

  method M(x: MyBool) returns (y: MyBool)
  {
    y := x;
    var z := x && !x ==> x;
    assert z;
  }

  method Test() {
    var b: MyBool := true;
    var c := M(b);
    var d: bool := c as bool;
    var e := M((2 < 19 < 17 < 19 <==> true as bool) as MyBool);
    var f := M((2 < 19 < 17 < 19 <==> true) as MyBool);
    var g := M(2 < 19 < 17 < 19);
    print b, " ", c, " ", e, " ", f, " ", g, "\n"; // true true false false false
    TestMore();
    Operators(true);
  }

  method TestMore() {
    var b: bool;
    var c: MyBool;
    c := b as MyBool;
    b := c as bool;

    var x: int;
    var y: MyInt;
    y := x as MyInt;
    x := y as int;

    print b, " ", c, " ", x, " ", y, "\n"; // false false 0 0

    b := x as MyInt == y;
    c := x == y as int;
    print b, " ", c, "\n"; // true true

    b := x as MyInt < y;
    c := x < y as int;
    print b, " ", c, "\n"; // false false
  }

  method Operators(b: MyBool) {
    print b == b && !(b != b) && (b <==> b) && (b ==> b) && (!b ==> b) && (b <== b) && (b <== !b) && (b && b) && (b || b), "\n"; // true
  }
}

module TrivialConstraint {
  export
    provides Test

  newtype MyBool = b: bool | true
  newtype MyInt = int

  method M(x: MyBool) returns (y: MyBool)
  {
    y := x;
    var z := x && !x ==> x;
    assert z;
  }

  method Test() {
    var b: MyBool := true;
    var c := M(b);
    var d: bool := c as bool;
    var e := M((2 < 19 < 17 < 19 <==> true as bool) as MyBool);
    var f := M((2 < 19 < 17 < 19 <==> true) as MyBool);
    var g := M(2 < 19 < 17 < 19);
    print b, " ", c, " ", e, " ", f, " ", g, "\n"; // true true false false false
    TestMore();
    Operators(true);
  }

  method TestMore() {
    var b: bool;
    var c: MyBool;
    c := b as MyBool;
    b := c as bool;

    var x: int;
    var y: MyInt;
    y := x as MyInt;
    x := y as int;

    print b, " ", c, " ", x, " ", y, "\n"; // false false 0 0

    b := x as MyInt == y;
    c := x == y as int;
    print b, " ", c, "\n"; // true true

    b := x as MyInt < y;
    c := x < y as int;
    print b, " ", c, "\n"; // false false
  }

  method Operators(b: MyBool) {
    print b == b && !(b != b) && (b <==> b) && (b ==> b) && (!b ==> b) && (b <== b) && (b <== !b) && (b && b) && (b || b), "\n"; // true
  }
}

module BaseTypesThatAreSubsetTypes {
  type X = x: int | true
  type Y = y: X | true

  newtype A = a: int | true
  newtype B = b: A | true

  newtype M = m: X | true
  newtype N = n: Y | true

  method Test() {
    var w: int := 99;

    var x: X := 100;
    var y: Y := 101;
    
    var a: A := 102;
    var b: B := 103;

    var m: M := 104;
    var n: N := 105;

    print w + x + y + a as int + b as int + m as X + n as X, "\n"; // 714
  }
}

module Char {
  newtype MyChar = char
  newtype UpperCase = ch | 'A' <= ch <= 'Z' witness 'D'

  method Test() {
    var c, u, r := Comparisons();
    print c, " ", u, " ", r, "\n"; // 'e' 'E' true
    MyString([u, u, u]);
    MyString("HELLO");
    Mix();
    GoodOl'Char('B');
  }
  
  method Comparisons() returns (c: MyChar, u: UpperCase, r: bool) {
    c := 'e';
    u := 'E';

    expect c == c;
    expect !(u != u);

    r := c < c;
    expect !r;
    r := c <= c;
    expect r;
    r := c >= c;
    expect r;
    r := c > c;
    expect !r;

    r := u <= u <= u;
    expect r;

    if c == 'f' && u == 'D' {
      expect false;
    }
  }

  method MyString(s: seq<UpperCase>) {
    if s != [] {
      var ch := s[|s| / 2];
      var charDiff := ch as char - 'A' + 'B';
      expect ch == 'Z' || (charDiff as UpperCase > ch);
      expect charDiff as int == ch as char as int + 1;
      print ch, " ", charDiff, "\n";
    }
  }

  newtype MyBool = bool
  newtype MyInt = int

  method Mix() {
    var c: MyChar := 'A';
    var u: UpperCase := 'B';
    var one: MyInt := 1;

    var b: MyBool := (u as MyChar - c) as char == one as int as char;
    // Note, in the following line, `[c]` prints as "['A']", not just "A", because the type is not seq<char> but seq<MyChar>
    print [c], " ", u, " ", one, " ", b, "\n"; // ['A'] 'B' 1 true
  }
  
  method GoodOl'Char(ch: char)
    requires 'A' <= ch < 'Z'
  {
    print ch, " "; // 'B'

    var c0 := ch as char;
    var c1 := c0 - 'A';
    var charDiff := c1 + 'B';
    print charDiff, " "; // 'C'

    var uc := charDiff as char;
    print uc, " "; // 'C'

    print uc > ch, "\n"; // true
  }
}

module TypeDescriptors {
  newtype UpperCase = ch | 'A' <= ch <= 'Z' witness 'F'
  newtype MyInt = x: int | true witness 365
  newtype Word = x: int | -3 <= x < 0x8000_0000 witness 400
  type SubChar = ch | 'a' <= ch <= 'z' witness 'g'

  method Test() {
    var d0, y0 := P<char>('a', 'a', 'A', 3, 4, 5, 'b');
    var d1, y1 := P<UpperCase>('A', 'a', 'A', 3, 4, 5, 'b');
    var d2, y2 := P<int>(3, 'a', 'A', 3, 4, 5, 'b');
    var d3, y3 := P<MyInt>(4, 'a', 'A', 3, 4, 5, 'b');
    var d4, y4 := P<Word>(5, 'a', 'A', 3, 4, 5, 'b');
    var d5, y5 := P<SubChar>('b', 'a', 'A', 3, 4, 5, 'b');

    print "(";
    print d0, " ", y0, ") (";
    print d1, " ", y1, ") (";
    print d2, " ", y2, ") (";
    print d3, " ", y3, ") (";
    print d4, " ", y4, ") (";
    print d5, " ", y5, ")\n";
  }

  method P<X(0)>(x: X, ch: char, uc: UpperCase, i: int, m: MyInt, w: Word, s: SubChar) returns (d: X, y: X) {
    print ch, " ", uc, " ", i, " ", m, " ", w, " ", s, " -- ", x, "\n";
    d, y := *, x;
  }
}

module PrintChars {
  newtype MyChar = char

  method Test() {
    var ch: char := 'c';
    var my: MyChar := 'm';

    print ch, " ", my, "\n"; // 'c' 'm'
    Print(ch, my);
  }

  method Print<X, Y>(x: X, y: Y) {
    print x, " ", y, "\n"; // 'c' 'm'
  }
}

module Bitvectors {
  newtype BV = b: bv5 | b != 23
  newtype Word = bv32
  newtype Big = b: bv1024 | true
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
  newtype MyReal = r: real | true

  datatype Color = Blue | Yellow
  trait RefTrait extends object { }
  class MyClass extends RefTrait { }

  type Subset = b: bv5 | b != 23

  method Test() {
    IntermediateExpressions();
    var _, _ := Operations(7, 0x1234_abcd, -6);
    Overflows();
    var _ := Shift(18, 1, 2, 3);
    var _, _ := Rotate(18, 2, 2, 3);
    BvZero(0);
    var _, _, _, _, _, _, _, _, _ := TestsAndConversions();

    var size := Comprehensions({9, 11}, {3}, {200, 190, 191}, {17} + {18});
    print size, "\n"; // 8
  }

  method IntermediateExpressions() {
    var fem: bv5 := 5;
    var sju: Subset := 4 + 3;
    var nio: BV := 1 + 8;

    assert fem == 5 && sju == 7 && nio == 9;
    print fem, sju, nio, "\n"; // 579
  }

  method Operations(x: BV, y: Word, z: Big) returns (r: bool, s: BV) {
    // ==
    r := x == x;
    r := y == y;
    r := z == z;

    r := x == 5;

    // + - * / %
    if x != 0 {
      s := x + x - x * (x / x - x % x);
      print s, " ";
    }
    if 3 <= x < 8 {
      s := 12 + x - (x + 19 / 17 - x % 3);
      print s, " ";
    }
    s := 12 + 13 - 14 * (15 + 16 / 17 - 18 % 19);
    print s, " ";

    // & | ^
    s := (x & x) | (x ^ x ^ x);
    print s, " "; // 7
    s := (12 & 13) | (14 ^ 15 ^ 16);
    print s, " ";

    // < <= >= >
    r := (x <= x && x < x) || x >= x || x > x;
    print r, "\n"; // true

    if !(x as bv5) != 23 {
      print "one's complement: ", !x, " ", !y, " ", !z, " "; // 24 3989525554 5
      print !(5 as bv7), " ", !(5 as bv3), " ", !(5 as bv8), "\n"; // 122 2 250
    }
    if -(x as bv5) != 23 {
      print "two's complement: ", -x, " ", -y, " ", -z, " "; // 25 3989525555 6
      print -(5 as bv7), " ", -(5 as bv3), " ", -(5 as bv8), "\n"; // 123 3 251
    }

    print "== bv: ", x == x, " ", y == y, " ", (5 as bv5) == (5 as BV) as bv5, " ", (4 as bv325) == (4 as bv325), "\n"; // true true true true
    print "== int: ", 5 == 5, " ", (5 as int32) == (5 as BV) as int32, " ", (5 as int32) == (5 as int32), "\n"; // true true true
    print "== real: ", 5.0 == 5.0, " ", (5.0 as MyReal) == (5.0 as MyReal), "\n"; // true true
    print "!= bv: ", x != x, " ", y != y, " ", (5 as bv5) != (5 as BV) as bv5, " ", (4 as bv325) != (4 as bv325), "\n"; // false false false false
    print "!= int: ", 5 != 5, " ", (5 as int32) != (5 as BV) as int32, " ", (5 as int32) != (5 as int32), "\n"; // false false false
    print "!= real: ", 5.0 != 5.0, " ", (5.0 as MyReal) != (5.0 as MyReal), "\n"; // false false
    print "<= bv: ", x <= x, " ", y <= y, " ", (5 as bv5) <= (5 as BV) as bv5, " ", (4 as bv325) <= (4 as bv325), "\n"; // true true true true
    print "<= int: ", 5 <= 5, " ", (5 as int32) <= (5 as BV) as int32, " ", (5 as int32) <= (5 as int32), "\n"; // true true true
    print "<= real: ", 5.0 <= 5.0, " ", (5.0 as MyReal) <= (5.0 as MyReal), "\n"; // true true

    var c0, c1 := new MyClass, new MyClass;
    var col0, col1, col2 := Blue, Yellow, Yellow;
    print "== class: ", c0 == c1, " ", c0 == c0, " / "; // false true /
    print (c0 as RefTrait) == (c1 as RefTrait), " ", (c0 as RefTrait) == (c0 as RefTrait), " / "; // false true /
    print (c0 as object) == (c1 as object), " ", (c0 as object) == (c0 as object), " ", (c0 as object) != (c0 as object), "\n"; // false true false
    print "== datatype: ", col0 == col1, " ", col1 == col2, " ", col2 == col2, " ", col1 != col2, "\n"; // false true true false
  }

  method Overflows()
  {
// SOON or never:
//    print (18 as bv5) + 19, " ", (18 as bv5) - 19, " ", (18 as bv5) * 19, "\n"; // 5 31 22 // TODO: Go complains about the overflow here
    var x: BV := 18;
    var x' := x + 1;
    print x + x', " ", x - x', " ", x * x', "\n"; // 5 31 22

// SOON or never:
//    print (0x8000_0002 as bv32) + 0x8000_0003, " "; // 5
//    print (0x8000_0002 as bv32) - 0x8000_0003, " "; // 4294967295
//    print (0x8000_0002 as bv32) * 0x8000_0003, "\n"; // 2147483654
    var w: Word := 0x8000_0002;
    var w' := w + 1;
    print w + w', " ", w - w', " ", w * w', "\n"; // 5 4294967295 2147483654
  }

  method Shift(x: BV, y: Word, b: bv32, i: int) returns (s: BV)
    requires 0 <= y < 5 && 0 <= b < 5 && 0 <= i < 5
  {
    var si: bv5 := (18 as bv5) << 1;
    print si, " "; // 4
    s := x << y;
    print s, " "; // 4
    s := x >> b;
    print s, " "; // 4
    s := x << i;
    print s, "\n"; // 16
  }
  
  method Rotate(x: BV, i: int, b: bv32, j: int32) returns (s: BV, a: bv5)
    requires 0 <= b < 5 && 0 <= i < 5 && 0 <= j < 5
  {
    a := x.RotateLeft(i);
    print a, " "; // 10
    
    a := x.RotateRight(b as int);
    print a, " "; // 20

    a := x.RotateRight(j as nat);
    print a, " "; // 10
    expect a == 10;
    s := x.RotateRight(j as nat) as BV;
    print s, "\n"; // 10
  }

  method BvZero(b: bv0) {
    var c: bv0 := *;

    print b + c, b - c, b * c, " ", !b, " ", -b, "\n"; // 000 0 0
    print b == c, " ", b != c, " ", b <= c, " ", b < c, " ", b >= c, " ", b > c, "\n"; // true false true false true false
    print b & c, b | c, b ^ c, " ", b << c, b << 0, b << 0 as int32, " ", b >> c, b >> 0, b >> 0 as int32, "\n"; // 000 000 000
    print b.RotateLeft(0), " ", b.RotateRight(0), " -- ", 0 as bv0, b as int, 0 as int32 as bv0, "\n"; // 0 0 -- 000
  }

  method TestsAndConversions() returns (x: BV, y: Word, z: Big, a: bv5, b: bv32, c: bv1024, i: int, j: int32, r: bool) {
    x := 10;
    x := x;
  
    r := y is Word;

    x := 10 as BV;
    x := x as BV;
    x := (if y < 20 then y else 2) as BV;
    print x, " "; // 0
    if a != 23 {
      x := a as BV;
    }

    b := 25;
    x := ((b & 0xF) * 2) as BV;
    print x, " "; // 18
    print (x as int as bv5) == x as bv5, "\n"; // true

    if 0 <= i <= j as int < 23 {
      x := i as BV;
      x := j as BV;
    }

    r := 10 is bv5;
    r := x is bv5;
    r := y is bv5;
    r := z is bv5;
    r := a is bv5;
    r := b is bv5;
    r := c is bv5;
    r := i is bv5;
    r := j is bv5;
  }

  newtype Bits = b: bv109 | Predicate(b)

  predicate Predicate(x: bv109) {
    true
  }

  method Comprehensions(aa: set<bv7>, bb: set<BV>, cc: set<Word>, dd: set<Bits>) returns (size: nat) {
    var se0, se1, se2, se3;
    se0 := set x | x in aa;
    se1 := set x | x in bb;
    se2 := set x | x in cc;
    se3 := set x | x in dd;
    return |se0| + |se1| + |se2| + |se3|;
  }
}

module SubsetTypeIsTests {
  type BV = b: bv5 | b != 23
  type Word = bv32
  type Big = b: bv1024 | true
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  datatype Color = Blue | Yellow
  trait RefTrait extends object { }
  class MyClass extends RefTrait { }

  type Subset = b: bv5 | b != 23

  method Test() {
    TestsAndConversions(0, 0, 0, 0, 0, 0, 0, 0);
    TestsAndConversions(24, 23, 23, 23, 23, 23, 23, 23);
    TestsAndConversions(24, 99, 99, 24, 99, 99, 99, 99);
    print "done\n";
  }

  method TestsAndConversions(x: BV, y: Word, z: Big, a: bv5, b: bv32, c: bv1024, i: int, j: int32) {
    print " ", 10 is bv5;
    print " ", x is bv5;
    print " ", y is bv5;
    print " ", z is bv5;
    print " ", a is bv5;
    print " ", b is bv5;
    print " ", c is bv5;
    print " ", i is bv5;
    print " ", j is bv5;
    print "\n";
  }
}


module NewtypeIsTests {
  newtype BV = b: bv5 | b != 23
  newtype Word = bv32
  newtype Big = b: bv1024 | true
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  datatype Color = Blue | Yellow
  trait RefTrait extends object { }
  class MyClass extends RefTrait { }

  type Subset = b: bv5 | b != 23

  method Test() {
    TestsAndConversions(0, 0, 0, 0, 0, 0, 0, 0);
    TestsAndConversions(24, 23, 23, 23, 23, 23, 23, 23);
    TestsAndConversions(24, 99, 99, 24, 99, 99, 99, 99);
    print "done\n";
  }

  method TestsAndConversions(x: BV, y: Word, z: Big, a: bv5, b: bv32, c: bv1024, i: int, j: int32) {
    print " ", 10 is bv5;
    print " ", x is bv5;
    print " ", y is bv5;
    print " ", z is bv5;
    print " ", a is bv5;
    print " ", b is bv5;
    print " ", c is bv5;
    print " ", i is bv5;
    print " ", j is bv5;
    print "\n";
  }
}

module NewBehaviors {
  newtype MyBool = bool
  newtype Word = bv32

  method Test() {
    TestIs(false, 0x4_0000_0000);
  }

  method TestIs(b: bool, x: int)
    requires !b && 0x1_0000_0000 <= x
  {
    var mIs: MyBool := b is MyBool;
    var mAs: MyBool := b as MyBool;
    var w0: bool := (x % 1000) is Word;
    var w1: MyBool := x is Word;

    print mIs, " ", mAs, " ", w0, " ", w1, "\n"; // true false true false
  }
}

module TypeParameters {
  newtype Wrapper<G> = g: G | true witness *
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  method Test() {
    var b: Wrapper<bool>;
    b := true ==> false;
    var i: Wrapper<Wrapper<int>>;
    i := Wrap3(25) as Wrapper<Wrapper<int>>;
    var j: Wrapper<Wrapper<Wrapper<int32>>>;
    j := Wrap3(30);
    print b, " ", i, " ", j, "\n"; // false 25 30

    print Unwrap3(j) < 2, " "; // false
    print Unwrap3(j) < 32, " | "; // true |
    var w: int32 := 299;
    b := Unwrap3(j) < w;
    print b, "\n"; // true
  }

  function Wrap3(x: int32): Wrapper<Wrapper<Wrapper<int32>>> {
    x as Wrapper<int32> as Wrapper<Wrapper<int32>> as Wrapper<Wrapper<Wrapper<int32>>>
  }

  function Unwrap3(x: Wrapper<Wrapper<Wrapper<int32>>>): int32 {
    x as Wrapper<Wrapper<int32>> as Wrapper<int32> as int32
  }
}

module AutoInit {
  newtype A<Unused> = x: int | 5 <= x witness 5
  newtype B<Unused> = z: real | true
  newtype Int32<Unused> = x | -0x8000_0000 <= x < 0x8000_0000 witness 7

  newtype pos = x: int | 0 < x witness 19

  method TestOne<X(0)>() {
    var x: X := *;
    print x, "\n";
  }

  method Test() {
    TestOne<A<pos>>(); // 5
    TestOne<B<pos>>(); // 0.0
    TestOne<Int32<pos>>(); // 7
  }
}

abstract module RefinementA {
  type AbstractType
  newtype NAT = AbstractType witness *
  newtype NATx = x: AbstractType | true witness *

  method Test(n: NAT, nx: NATx) {
    print n, " ", nx, "\n";
  }
}

module RefinementB refines RefinementA {
  type AbstractType = real
}

module SimpleNewtypeWitness {
  newtype A = x: int | 100 <= x witness 102
  newtype B = a: A | true witness 103
  newtype C = A witness 104

  method Test() {
    var a: A := *;
    var b: B := *;
    var c: C := *;
    print a, " ", b, " ", c, "\n"; // 102 103 104
  }
}

module CharToInt {
  newtype char16 = c: char | c as int < 65536

  method Test() {
    var c: char := 'c';
    var d: char16 := 'd';

    print c, " (", c as int, ", ", c as char as int, "), ";
    print d, " (", d as int, ", ", d as char as int, ")\n";
  }
}
