// RUN: %exits-with 4 %build --type-system-refresh true --general-newtypes true --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module EmptyBool {
  newtype MyBool = bool
  newtype AnyBool = b: bool | true
  newtype NoBool = b: bool | false witness *

  method M0(a: MyBool, b: AnyBool) {
    assert false; // error
  }

  method M1(c: NoBool) {
    assert false;
  }

  method Test() {
    var a: MyBool := true;
    var b: AnyBool := true;
    var c: NoBool := true; // error: not a NoBool
    Recursive(true);
    NonStop(true);
  }

  method Recursive(x: AnyBool) {
    if x {
      Recursive(!x);
    }
  }

  method NonStop(x: AnyBool) {
    NonStop(!x); // error: termination failure
  }

  method Stops(x: AnyBool) {
    if x {
      Stops(!x);
    }
  }

  method AllCases(m: MyBool, a: AnyBool) {
    if
    case !m && !a as MyBool =>
    case !m as AnyBool && a =>
    case m as bool && !a as bool as AnyBool as bool =>
    case m as bool as AnyBool && a =>
  }
}

module TrueBoolModule {
  newtype TrueBool = b | b witness true

  method M(x: TrueBool) returns (y: TrueBool)
  {
    assert x;
    y := x;
    var z := x ==> x;
    assert z;
  }

  method Test() {
    var b: TrueBool := true;
    var c := M(b);
    var d: bool := c as bool;
    var e := M(2 < 19);
    print b, " ", c, " ", e, "\n"; // true true true
    Recursive(true);
  }

  method Literals() {
    var x: TrueBool;
    x := true;
    x := false; // error: false is not a TrueBool
  }

  method Recursive(x: TrueBool)
    decreases x
  {
    var b := x as bool;
    if !b {
      assert false; // we never get here
      Recursive(false);
    }
  }

  method IntermediateExpressions0(x: TrueBool) {
    while x {
      break;
    }
    while {
      case false =>
      case x => break;
      case true => break;
    }

    if
    case true =>
      var u := x && !x; // error: !x is not a TrueBool
    case x =>
      var u := (!(x as bool) || x as bool) as TrueBool;
  }

  newtype FalseBool = b | !b

  method IntermediateExpressions1(x: TrueBool, y: FalseBool) {
    if * {
      var _ := true && (x <==> x);
    } else if * {
      var _ := false || (y <==> y); // error: (y <==> y) is not a FalseBool
    } else if * {
      var _ := (true && x == x && !(y == y)) || false; // result is a bool, so anything goes
    } else if * {
      var a: TrueBool := true && x == x;
    } else if * {
      var _ := false || y == y; // result is a bool, so anything goes
      var z: bool := false || y == y; // result is a bool, so anything goes
      var b: FalseBool := false || y == y; // error: (y == y) is not a FalseBool
    } else if * {
      var a: TrueBool := true && y != y; // error: (y != y) is not a TrueBool
    } else if * {
      var b: FalseBool := false || x != x;
    }
  }

  method IntermediateExpressions2(x: TrueBool, y: FalseBool) {
    if * {
      var _ := x ==> !x; // error: !x is not a TrueBool
    } else if * {
      var _ := x <== !x; // error: !x is not a TrueBool
    } else if * {
      var _ := y ==> !y; // error: (y ==> !y) is not a FalseBool
    } else if * {
      var _ := y <== !y; // error: !y is not a FalseBool
    }
  }

  method IntermediateExpressions3(x: TrueBool, y: FalseBool) {
    if * {
      var _ := x && x;
      var _ := x || x;
      var _ := y && y;
      var _ := y || y;
    } else if * {
      var _ := true && x && x;
      var _ := false || x || x; // error: false is not a TrueBool
    } else if * {
      var _ := y || false || y;
      var _ := y && y && true;
      var _ := y || true || y; // error: true is not a FalseBool
    } else if * {
      var a0 := if x then x else !x;
      var a1: FalseBool := if x then y else !y;
      var a2 := if y then !y else y;
      var a3 := if y then x else !x; // error: !x is not a TrueBool
    }
  }

  codatatype Stream = More(Stream)

  method IntermediateExpressions4(s: Stream, k: nat, o: ORDINAL, i: int) returns (ghost x: TrueBool, ghost y: FalseBool) {
    if
    case true =>
      x := s ==#[k] s;
    case true =>
      x := s ==#[o] s;
    case true =>
      x := s !=#[k] s; // error: RHS is not a TrueBool
    case true =>
      x := s !=#[o] s; // error: RHS is not a TrueBool
    case true =>
      y := s ==#[k] s; // error: RHS is not a FalseBool
    case true =>
      y := s ==#[o] s; // error: RHS is not a FalseBool
    case true =>
      y := s !=#[k] s;
    case true =>
      y := s !=#[o] s;
    case true =>
      x := s ==#[i] s; // error: i may be negative
  }
}

module NewtypesAreDistinctFromBaseType {
  newtype MyBool = bool
  newtype AnotherBool = b: MyBool | true
  type JustASubsetType = b: MyBool | true

  method M(a: array<bool>, b: array<MyBool>, c: array<AnotherBool>, d: array<JustASubsetType>) {
    assert a != b as object;
    assert a as object != b;

    assert b != c as object;
    assert b != d as object;
    assert c != d as object;

    assert false; // error
  }

  newtype TrueAsCanBe = b: bool | b witness true

  method P<K>(i: int, a: array<TrueAsCanBe>, s: set<TrueAsCanBe>, k: K, m: map<K, TrueAsCanBe>)
  {
    if 0 <= i < a.Length {
      assert a[i];
    }
    assert |s| <= 1 by {
      assert s <= {true};
      assert s == {} || s == {true};
    }
    if k in m.Keys {
      assert m[k];
    }
  }
}

module Char {
  newtype MyChar = char
  newtype UpperCase = ch | 'A' <= ch <= 'Z' witness 'D'

  method Comparisons() returns (c: MyChar, u: UpperCase, r: bool) {
    c := 'e';
    u := 'E';

    assert c == c;
    assert !(u != u);

    r := c < c;
    assert !r;
    r := c <= c;
    assert r;
    r := c >= c;
    assert r;
    r := c > c;
    assert !r;

    r := u <= u <= u;
    assert r;

    if c == 'f' && u == 'D' {
      assert false;
    }
  }

  method MyString(s: seq<UpperCase>) {
    if s != [] {
      var ch := s[|s| / 2];
      var diff := ch - 'A' + 'A'; // error: result of '-' is not an UpperCase
      var charDiff := ch as char - 'A' + 'B';
      assert ch == 'Z' || (charDiff as UpperCase > ch);
      assert charDiff as int == ch as char as int + 1;
    }
  }
}

module Chars {
  newtype MyChar = ch: char | ch != 'b'
  newtype Char = char

  type Subset = ch: char | ch != 'b'

  method Conversions() returns (s: Subset, x: MyChar, y: Char, a: char) {
    if
    case true =>
      a := a as char;
    case true =>
      a := a as Subset; // error: may violate constraint
    case true =>
      x := a as MyChar; // error: may violate constraint
    case true =>
      y := a as Char;
    case true =>
      x := y as MyChar; // error: may violate constraint
  }

  type NotRSubset = ch: char | ch != 'r'
  newtype NotRNewtype = ch: char | ch != 'r'

  method TestCharSubset() returns (ch: char, nr: NotRSubset) {
    if
    case true =>
      ch := nr as char;
    case true =>
      nr := ch as NotRSubset; // error: might be 'r'
    case ch != 'r' =>
      nr := ch as NotRSubset;
  }
  
  method TestCharNewtype() returns (ch: char, nr: NotRNewtype) {
    if
    case true =>
      ch := nr as char;
    case true =>
      nr := ch as NotRNewtype; // error: might be 'r'
    case ch != 'r' =>
      nr := ch as NotRNewtype;
  }
}

module Bitvectors {
  newtype BV = b: bv5 | b != 23
  newtype Word = bv32
  newtype Big = b: bv1024 | true
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  type Subset = b: bv5 | b != 23

  method IntermediateExpressions() {
    var fem: bv5 := 5;
    var sju: Subset := 4 + 3;
    var nio: BV := 1 + 8;

    assert fem == 5 && sju == 7 && nio == 9;

    assert 25 - 2 - 16 == 7;
    sju := 25 - 2 - 16; // fine
    assert 25 - 2 - 14 == 9;
    nio := 25 - 2 - 14; // error: 25 - 2 violates the newtype constraint
  }

  method Operations(x: BV, y: Word, z: Big, a: bv5, b: bv32, c: bv1024, i: int, j: int32) returns (r: bool, s: BV) {
    // ==
    r := x == x;
    r := y == y;
    r := z == z;

    r := x == 5;

    // + - * / %
    s := x + x - x * (x / x - x % x); // error: division by zero (but, amazingly, no intermediate expression is 23)
    s := 12 + x - x * (x + 19 / 17 - x % 3); // error (x2): two of the intermediate expressions might be 23
    s := 12 + 13 - 14 * (15 + 16 / 17 - 18 % 19);

    // & | ^
    s := (x & x) | (x ^ x ^ x);
    s := (12 & 13) | (14 ^ 15 ^ 16);

    // < <= >= >
    r := (x <= x && x < x) || x >= x || x > x;
    assert r; // since x >= x

    if !(x as bv5) != 23 && -(x as bv5) != 23 {
      assert !!x == x && !!y == y && z == !!z && !z == !z;
      assert --x == x && --y == y && z == --z && -z == -z;
    }
    assert !(5 as bv7) == 122 && !(5 as bv3) == 2 && !(5 as bv8) == 250;
    assert -(5 as bv7) == 123 && -(5 as bv3) == 3 && -(5 as bv8) == 251;
  }

  method Shift(x: BV, y: Word, z: Big, a: bv5, b: bv32, c: bv1024, i: int, j: int32) returns (r: bool, s: BV) {
    // << >>
    s := x << y; // error: shift amount might be larger than 5
    s := x >> b; // error: shift amount might be larger than 5
    if i < 5 {
      s := x << i; // error: shift amount might be negative
    }
  }
  
  method Rotate(x: BV, b: bv32, i: int, j: int32) returns (r: bool, s: BV, a: bv5) {
    //  .RotateLeft .RotateRight
    if i < 5 {
      a := x.RotateLeft(i); // error: argument to RotateLeft might be negative
    }
    
    a := x.RotateRight(b as int); // error: argument to RotateRight might be too big

    if j < 5 {
      a := x.RotateRight(j as nat); // error: cast to BV might fail
    }

    if 0 <= j < 5 {
      s := x.RotateRight(j as nat) as BV; // error: cast to BV might fail
    }
  }

  method BvZero(b: bv0) returns (d: bv0) {
    var c: bv0 := *;

    d := b + c;
    d := b - c;
    d := b * c;
    d := !b;
    d := -b;
    assert b == c && !(b != c) && b <= c && b >= c && !(b < c) && !(b > c);
    d := b & c;
    d := b | c;
    d := b ^ c;
    d := b << c;
    d := b << 0;
    d := b << 0 as int32;
    d := b >> c;
    d := b >> 0;
    d := b >> 0 as int32;
    d := b.RotateLeft(0);
    d := b.RotateRight(0);
    d := 0 as bv0;
    var i := b as int;
    d := 0 as int32 as bv0;
  }

  method TestsAndConversions() returns (x: BV, y: Word, z: Big, a: bv5, b: bv32, c: bv1024, i: int, j: int32, r: bool) {
    x := 10;
    x := x;
  
    r := y is Word;

    if * {
      x := 10 as BV;
      x := x as BV;
      x := (if y < 20 then y else 2) as BV;
      if a != 23 {
        x := a as BV;
      }

      ghost var bx := b & 0xF;
      assert bx < 16;
      ghost var bz := bx * 2;
      assert bz < 32;
      assert bz % 2 == 0;
      x := ((b & 0xF) * 2) as BV;

      if 0 <= i <= j as int < 23 {
        x := i as BV;
        x := j as BV;
      }

    } else {
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
  }

  newtype GhostBits = b: bv109 | GhostPredicate(b)

  ghost predicate GhostPredicate(x: bv109) {
    true
  }

  method Comprehensions(aa: set<bv7>, bb: set<BV>, cc: set<Word>, dd: set<GhostBits>) {
    var se0, se1, se2;
    ghost var se3;
    se0 := set x | x in aa;
    se1 := set x | x in bb;
    se2 := set x | x in cc;
    se3 := set x | x in dd;
  }
}

module TypeParametersForNewtype {
  newtype Wrapper<G> = g: G | true witness *
  method CallMe<U>(u: Wrapper<U>) returns (v: Wrapper<U>)

  method Test(x: bool) returns (y: Wrapper<bool>) {
    var b: Wrapper<bool>;
    b := x as Wrapper<bool>;
    y := CallMe(b);
  }
}

module TypeParametersForSubsetType {
  type Wrapper<G> = g: G | true witness *
  method CallMe<U>(u: Wrapper<U>) returns (v: Wrapper<U>)

  method Test(x: bool) returns (y: Wrapper<bool>) {
    var b: Wrapper<bool>;
    b := x as Wrapper<bool>;
    y := CallMe(b);
  }
}

module TypeParametersForTypeSynonym {
  type Wrapper<G> = G
  method CallMe<U>(u: Wrapper<U>) returns (v: Wrapper<U>)

  method Test(x: bool) returns (y: Wrapper<bool>) {
    var b: Wrapper<bool>;
    b := x as Wrapper<bool>;
    y := CallMe(b);
  }
}

module ExpandToTypeParameterWithoutWitness {
  // The following two lines once had caused a crash in the verifier
  type A<Y> = y: Y | true // error: 
  newtype B<Z> = z: Z | true // error: 
}

module AutoInitValueSubsetType {
  type Never = x: int | false witness *
  type Impossible = n: Never | true // error: default witness 0 does not satisfy constraint of base type

  method Test() {
    var x: Impossible := *;
    assert false;
    print 10 / x;
  }
}

module AutoInitValueNewtype {
  newtype Never = x: int | false witness *
  newtype Impossible = n: Never | true // error: default witness 0 does not satisfy constraint of base type

  method Test() {
    var x: Impossible := *;
    assert false;
    print 10 / x;
  }
}

module AutoInitValueNewtypeWithoutVar {
  newtype Never = x: int | false witness *
  newtype Impossible = Never // error: default witness 0 does not satisfy constraint of base type

  method Test() {
    var x: Impossible := *;
    assert false;
    print 10 / x;
  }
}

module BaseTypeConstraintHelpsWellformednessSubsetType {
  predicate P(x: NotSeven)
    requires x != 6
  {
    true
  }

  type NotSeven = x: int | x != 7 witness *
  type Okay = n: NotSeven | P(if 8 <= n then n else n - 1)
  type NotWellformed = n: NotSeven | P(n) // error: precondition violation
}

module BaseTypeConstraintHelpsWellformednessNewtype {
  predicate P(x: NotSeven)
    requires x != 6
  {
    true
  }

  newtype NotSeven = x: int | x != 7 witness *
  newtype Okay = n: NotSeven | P(if 8 <= n then n else n - 1)
  newtype NotWellformed = n: NotSeven | P(n) // error: precondition violation
}

module SimpleNewtypeWitness {
  newtype A = x: int | 100 <= x witness 102
  newtype B = a: A | true witness 103

  newtype C = A // error: default witness 0 does not satisfy constraint
  newtype D = A witness 104
  newtype E = A ghost witness 104
  newtype F = A witness *

  newtype G = A witness 13 // error: 13 does not satisfy constraint
  newtype H = A ghost witness 13 // error: 13 does not satisfy constraint
}

module StringLiterals {
  newtype LowerCase = ch: char | 'a' <= ch <= 'z' witness 'a'
  newtype MyChar = ch: char | 'a' <= ch <= 'z' || ch == '\n' witness 'a'
  newtype MyString = s: seq<MyChar> | |s| < 5

  method BadCharacters() {
    if
    case true =>
      var w0: MyString := "";
    case true =>
      var w1: MyString := "rs";
    case true =>
      var w2: MyString := ['r', 's'];
    case true =>
      var w3: MyString := ['r', 'A']; // error: 'A' is not a MyChar
    case true =>
      var w4: MyString := "rB"; // error: 'B' is not a MyChar
    case true =>
      var w5: seq<MyChar> := ['r', 'C']; // error: 'C' is not a MyChar
    case true =>
      var w6: seq<MyChar> := "rD";  // error: 'D' is not a MyChar
  }

  method BadVerbatim() {
    if
    case true =>
      var w0: seq<LowerCase> := @"r
s"; // error (on previous line): the newline is not a LowerCase
//    case true =>
//      var w1: seq<MyChar> := @"r
//s";
//   case true =>
//      var w2: MyString := @"r
//Xs"; // error (on previous line): 'X' is not a MyChar
   case true =>
      var w3: MyString := @"r
stuvxyz"; // error (on previous line): too long to be a MyString
    case true =>
      var w4: seq<char> := @"
abcdeABCDE";
  }

  method BadStringLength() {
    if
    case true =>
      var w0: MyString := "abcde"; // error: too long to be a MyString
    case true =>
      var w1: MyString := ['r', 's', 't', 'u', 'v']; // error: too long to be a MyString
  }

  method BadChar() {
    if
    case true =>
      var ch0: char := 'a';
      var ch1: LowerCase := 'a';
      var ch2: MyChar := 'a';
    case true =>
      var ch3: char := 'X';
    case true =>
      var ch4: LowerCase := 'Y'; // error: not a LowerCase
    case true =>
      var ch5: MyChar := 'Z'; // error: not a MyChar
  }
}

/*
module RealConversions {
  method TestRealIsInt0(r: real)
    requires r.Floor as real == r
  {
    if
    case true =>
      var _ := r as int;
    case true =>
      assert r is int;
  }

  method TestRealIsInt1(r: real)
    requires r is int
  {
    if
    case true =>
      var _ := r as int;
    case true =>
      assert r.Floor as real == r;
  }
}
*/
