// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module LiteralSizes {
  method M(a: bv1, b: bv32) returns (c: bv32, d: bv1)
  {
    c := b;
    d := a;
    var x := 5000;  // error: number too big
    d := x;
    var y := 4000;
    y := c;
    var z: bv0;
    z := 0;
    z := 1;  // error: number too big
    c := 0x8000_0000;
    c := 0xFFFF_FFFF;
    c := 0x1_0000_0000;  // error: number too big

    var b67: bv67, w: bv32, seven: bv7, noll: bv0;
    b67 := 1 << 3;
    w := 1 << 3;
    seven := 1 << 3;
    noll := 1 << 3;  // error: number too big
  }
}

module OrdinaryTypeChecking {
  newtype EvenInt = x | x % 2 == 0
  newtype SmallReal = r | -4.0 <= r < 300.0
  newtype Handful = x | 0 <= x < 0x50

  method Shifts() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0, h: Handful)
  {
    x := b67 << 3;  // error: result not assignable to an int
    x := b67 << 3 as int;  // error: ditto (the "as" applies only to the "3")
    x := (b67 << 3) as int;
    x := b67.RotateLeft(3); // error: bitwise rotations produce bitvectors
    x := b67.RotateRight(3); // error: ditto
    b67 := b67 << r;  // error: cannot shift by a real
    b67 := b67 << small;  // error: cannot shift by a real
    b67 := b67.RotateLeft(r);
    b67 := b67.RotateLeft(small);
    b67 := b67 << x;
    b67 := b67 << n;
    b67 := b67 << h;
    b67 := b67 << even;

    b67 := b67 << b67;
    b67 := b67 << w;
    b67 := b67 << seven;
    b67 := b67 << noll;

    w := w << b67;
    w := w << w;
    w := w << seven;
    w := w << noll;

    seven := seven << b67;
    seven := seven << w;
    seven := seven << seven;
    seven := seven << noll;

    noll := noll << b67;
    noll := noll << w;
    noll := noll << seven;
    noll := noll << noll;

    b67 := 1 << 3;
    w := 1 << 3;
    seven := 1 << 3;
    noll := 1 << 3;
  }
}

module ParsingRegression0 {
  // Top-level expressions inside a cardinality expression are not allowed to
  // use the bitwise-or operator, but this rule should also extend to end-less
  // expressions like "if", "match", let, statement expressions, and
  // comprehensions.
  method M(s: seq<int>, t: seq<int>, u: seq<int>, bit: bv1) returns (x: int, c: Color) {
    x := |if 5 in s then s else t|;  // the last "|" was previously flagged as a parsing error
    x := if 5 in s then |s| else |t|;
    x := |if 5 in s then if |u| == 17 then u else s else t|;

    x := |match c case Yellow => s|;
    x := |match c case Yellow => s case Green => if 5 in s then s else t|;
    x := |match c case Yellow => s case Green => if 5 in s then s else t case Red => u|;

    x := |assert true; s|;

    x := |var w := s; s|;

    x := |set k | 0 <= k < 100 :: k < 100|;
    x := |set k | 0 <= k < 100|;
    x := |map k | 0 <= k < 100 :: k|;
    // note, you can't take the cardinality of an iset or imap, so they can be allowed bitwise ops
    var s0 := iset k | 0 <= k < 100 :: bit | 1;
    var s1 := iset k | k in {0,1} && k != bit | 1;
    var m0 := imap k | 0 <= k < 100 :: bit | 1;
  }
  datatype Color = Yellow | Green | Red
}
module ParsingRegression1 {
  datatype Color = Yellow | Green | Red
  method M(c: Color)
  {
    // the following parses fine, but doesn't type check, since the type of the
    // set given to the cardinality operator is not determined
    var x: int := |match c|;  // error: type of set is underspecified
  }
}
