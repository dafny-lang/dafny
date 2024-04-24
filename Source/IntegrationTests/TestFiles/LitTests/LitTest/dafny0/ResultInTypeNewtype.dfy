// RUN: %exits-with 4 %verify --type-system-refresh --general-newtypes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests that the results of operations that create values of a newtype satisfy the newtype constraint.
// See also ResultInTypeSubsetType.dfy for the analogous tests for subset types.

module Bool {
  newtype False = b: bool | !b
  newtype True = b: bool | b // error: cannot find witness

  method Construct() returns (b: False) {
    b := true; // error: true is not a False
  }

  method Operators(f: False) returns (b: False) {
    if
    case true =>
      b := !f; // error: RHS is not a False
    case true =>
      b := f ==> f; // error: RHS is not a False
    case true =>
      b := f <== f; // error: RHS is not a False
    case true =>
      b := f <==> f; // error: RHS is not a False
    case true =>
      b := f == f; // error: RHS is not a False
  }

  method Is() returns (b: False) {
    var f: real := 3.0;
    b := f is int; // error: RHS is not a False
  }

  method As(a: bool) returns (b: False) {
    b := a as False; // error: RHS is not a False
  }

  method Fresh() returns (ghost b: False) {
    var c := new object;
    b := fresh(c); // error: RHS is not a False
  }
  
  ghost method QuantifierForall() returns (q: False) {
    q := forall x :: 0 <= 2 * x < 0 ==> true; // error: the RHS is true, which is not a False
  }

  ghost method QuantifierExists() returns (q: False) {
    var y := 3;
    assert 0 <= 2 * y < 10;
    q := exists x :: 0 <= 2 * x < 10; // error: the RHS is true, which is not a False
  }
}

module Int {
  newtype Int = x: int | 2 <= x < 4 // error: cannot find witness

  method Construct() returns (r: Int) {
    r := 20; // error: RHS not an Int
  }

  method Operators(x: Int, y: Int) returns (r: Int) {
    if
    case true =>
      r := -x; // error: RHS not an Int
    case true =>
      r := x + y; // error: RHS not an Int
    case true =>
      r := x - y; // error: RHS not an Int
    case true =>
      r := x * y; // error: RHS not an Int
    case true =>
      r := x / y; // error: RHS not an Int
  }

  method As(x: int) returns (r: Int) {
    r := x as Int; // error: RHS is not an Int
  }
}

module Real {
  newtype Real = x: real | 2.0 <= x < 4.0 // error: cannot find witness

  method Construct() returns (r: Real) {
    r := 20.0; // error: RHS not a Real
  }

  method Operators(x: Real, y: Real) returns (r: Real) {
    if
    case true =>
      r := -x; // error: RHS not a Real
    case true =>
      r := x + y; // error: RHS not a Real
    case true =>
      r := x - y; // error: RHS not a Real
    case true =>
      r := x * y; // error: RHS not a Real
    case true =>
      r := x / y; // error: RHS not a Real
  }

  method As(x: real) returns (r: Real) {
    r := x as Real; // error: RHS is not a Real
  }
}

module Bv {
  newtype Bv = x: bv7 | 2 <= x < 5 // error: cannot find witness

  method Construct() returns (r: Bv) {
    r := 20; // error: RHS not a Bv
  }

  method Operators(x: Bv, y: Bv) returns (r: Bv) {
    if
    case true =>
      r := -x; // error: RHS not a Bv
    case true =>
      r := x + y; // error: RHS not a Bv
    case true =>
      r := x - y; // error: RHS not a Bv
    case true =>
      r := x * y; // error: RHS not a Bv
    case true =>
      r := x / y; // error: RHS not a Bv
  }

  method BitwiseOperators(x: Bv, y: Bv) returns (r: Bv) {
    if
    case true =>
      r := !x; // error: RHS not a Bv
    case true =>
      r := x & y; // error: RHS not a Bv
    case true =>
      r := x | y; // error: RHS not a Bv
    case true =>
      r := x ^ y; // error: RHS not a Bv
  }

  method Shifts(x: Bv, y: Bv) returns (r: Bv) {
    if
    case true =>
      r := x << 1; // error: RHS not a Bv
    case true =>
      r := x >> 1; // error: RHS not a Bv
  }
  
  method As(x: bv7) returns (r: Bv) {
    r := x as Bv; // error: RHS is not a Bv
  }
}

module Char {
  newtype Char = x: char | 'a' <= x < 'e' // error: cannot find witness

  method Construct() returns (r: Char) {
    r := 'z'; // error: RHS not a Char
  }

  method Operators(x: Char, y: Char) returns (r: Char) {
    if
    case true =>
      r := x + y; // error: RHS not a Char
    case true =>
      r := x - y; // error (x2): possible underflow, and RHS not a Char
  }

  method As(x: char) returns (r: Char) {
    r := x as Char; // error: RHS is not a Char
  }
}

module Set {
  newtype IntSet = s: set<int> | |s| == 3 // error: cannot find witness

  method Construct() returns (s: IntSet) {
    if
    case true =>
      s := {}; // error: too small
    case true =>
      s := {6, 19, 20, 21, 22}; // error: too big
    case true =>
      s := {2, 3, 4}; // Goldilocks!
    case true =>
      s := set x: int | 2 <= x < 3 && 2 * x < 300; // error: too small
    case true =>
      s := set x: int | 2 <= x < 3 :: 2 * x; // error: too small
  }

  method Operators(a: IntSet, b: IntSet, m: set<int>) returns (s: IntSet) {
    if
    case true =>
      s := a + b; // error: may be too big
    case true =>
      s := a - b; // error: may be too small
    case true =>
      s := a * b; // error: may be too small
    case true =>
      s := m as IntSet; // error: may be of the wrong size
  }
}

module Iset {
  newtype IntIset = s: iset<int> | 2 in s <==> 3 !in s // error: cannot find witness

  method Construct() returns (s: IntIset) {
    if
    case true =>
      s := iset{2, 3}; // error: not an IntIset
    case true =>
      s := iset{6, 8}; // error: not an IntIset
    case true =>
      s := iset{2};
    case true =>
      s := iset x: int | 0 <= x < 5 && 2 * x < 300; // error: not an IntIset
    case true =>
      s := iset x: int | 2 <= x < 5 :: 2 * x; // error: not an IntIset
  }

  method Operators(a: IntIset, b: IntIset, m: iset<int>) returns (s: IntIset) {
    if
    case true =>
      s := a + b; // error: not an IntIset
    case true =>
      s := a - b; // error: not an IntIset
    case true =>
      s := a * b; // error: not an IntIset
    case true =>
      s := m as IntIset; // error: not an IntIset
  }
}

module Multiset {
  newtype Multiset = s: multiset<int> | s[2] + s[3] == 1 // error: cannot find witness

  method Construct() returns (s: Multiset) {
    if
    case true =>
      s := multiset{2, 2}; // error: not a Multiset
    case true =>
      s := multiset{6, 8}; // error: not a Multiset
    case true =>
      s := multiset{2};
  }

  method Operators(a: Multiset, b: Multiset, m: multiset<int>) returns (s: Multiset) {
    if
    case true =>
      s := a + b; // error: not a Multiset
    case true =>
      s := a - b; // error: not a Multiset
    case true =>
      s := a * b; // error: not a Multiset
    case true =>
      s := m as Multiset; // error: not a Multiset
  }

  method Conversion(t: set<int>, q: seq<int>) returns (s: Multiset) {
    if
    case true =>
      s := multiset(t); // error: not a Multiset
    case true =>
      s := multiset(q); // error: not a Multiset
    case true =>
      s := multiset({2});
  }
}

module Seq {
  newtype Seq = s: seq<int> | |s| == 3 // error: cannot find witness
  newtype String = s: string | |s| == 3 witness "abc"

  method Construct() returns (s: Seq, g: String) {
    s, g := [8, 8, 8], ['u', 'v', 'w'];
    if
    case true =>
      s := [2, 2]; // error: not a Seq
    case true =>
      s := [8, 7, 6];
    case true =>
      g := "xyz";
    case true =>
      g := "klmn"; // error: not a String
  }

  method Operators(a: Seq, b: Seq, m: seq<int>) returns (s: Seq) {
    if
    case true =>
      s := a + b; // error: not a Seq
    case true =>
      s := m as Seq; // error: not a Seq
  }

  method SubSequenceFromSeq(a: Seq) returns (s: Seq) {
    if
    case true =>
      s := a[..2]; // error: not a Seq
    case true =>
      s := a[2..]; // error: not a Seq
    case true =>
      s := a[1..2]; // error: not a Seq
    case true =>
      s := a[..];
  }

  method SubSequenceFromArray(a: array<int>) returns (s: Seq)
    requires 3 <= a.Length
  {
    if
    case true =>
      s := a[..2]; // error: not a Seq
    case true =>
      s := a[2..]; // error: not a Seq
    case true =>
      s := a[1..2]; // error: not a Seq
    case true =>
      s := a[..]; // error: not a Seq
  }
}
