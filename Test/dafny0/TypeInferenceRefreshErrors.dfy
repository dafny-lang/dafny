// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Frames {
  class C {
    var x: int
    var y: int
  }

  // The following was accepted by the old type checking, but it caused a crash in the
  // translator. Now, we disallow it.
  function ToC(): C
  function RegressionTest(): int
    reads ToC // error: type not allowed: () -> C

  function ToSetReal(): set<real>
  function ToMap(): map<object, object>
  function F(r: real, s: set<real>): int
    reads r // error: not a reference type
    reads s // error: not a collection of reference type
    reads ToSetReal // error: not a function to a collection of reference type
    reads ToMap // error: not a function to a collection of reference type
}

module As {
  class C { }
  class D { }
  method M(c: C, d: D, obj: object) {
    var cc: C;
    var dd: D;
    cc := obj as C;
    dd := obj as D;
    cc := d as C; // error: incompatible types
    dd := c as D; // error: incompatible types
  }
}

module Underspecification0 {
  method P() {
    var u; // error: type is underspecified
    var w := !u; // error: type is underspecified
  }
}

module Underspecification1 {
  class E<T> { }

  /* SOON
  method M(obj: object) {
    var ee := obj as E; // error: type parameter of E is underspecified
    assert (obj as E) == (obj as E); // error: type parameter of E is underspecified
    assert (obj as E) == (obj as E<set>); // error: type parameter of set is underspecified
    assert (obj as E) == (obj as E<set<int>>);
  }
  */
}

module Underspecification2 {
  method Q(m: map, n: map) { // fine, because of type-parameter elision rules
    var o := m + n;
  }

  method R() {
    var m: map; // error: type is underspecified
    var n: map; // error: type is underspecified
    var o; // error: type is underspecified
    o := m + n; // error: type of + is underspecified
  }
}

module Underspecification3 {
  datatype Option<X> = None | Some(X)

  type Synonym<X, Unused> = seq<X>

  type SubsetType<X, Unused> = s: seq<X> | |s| == 0

  method Underspecification() {
    // Regression: In the old type inference, the following line was not considered to be an error.
    var d: Synonym := [100, 101]; // error: type underspecified

    // Regression: In the old type inference, the following would pass and would then crash the verifier:
    var e: SubsetType := [100, 101]; // error: type underspecified
  }
}

/*
 * The following example causes Dafny 4.0 to crash (after reporting the expected error).

datatype R = R(int, int)

method M() {
  var pair: (int, int) := (20, 30);
  match pair
  case R(x, y) => // bogus: should not be allowed to match a pair against an R constructor
    print x + y, "\n";
}
 */

/* An additional match test

method TupleTests(d: bv7) {
  match d {
    case (y) => // error: parentheses not allowed around pattern
  }
}

 */

/*
module TooLargeCaseLiteral {
  method Test(bv: bv7) {
    match bv {
      case 84848484848484848 => // error (BUG: this is missed by Dafny 4.0)
      case _ =>
    }
  }
}

module CaseLiteralWrongType {
  method Test(bv: bv7, r: real) {
    match bv {
      case 2.18 => // error: wrong type // BUG: crashes Dafny 4.0
    }
    match r {
      case 13 => // error: wrong type
      case -0 => // error: wrong type
      case 0 => // error: wrong type
    }
    match r {
      case 15 => // error: wrong type // BUG: causes malformed Boogie in Dafny 4.0
      case -15 => // error: wrong type // BUG: causes malformed Boogie in Dafny 4.0
      case -0 => // error: wrong type // BUG: causes malformed Boogie in Dafny 4.0
      case false => // error: wrong type // BUG: causes malformed Boogie in Dafny 4.0
    }
  }
}

module NegativeCaseLabels {
  newtype int8 = x | -128 <= x < 128

  method NegativeLabels(a: int, nt: int8, bv: bv7, o: ORDINAL, r: real) {
    match a {
      case -3 =>
      case -0 =>
      case 0 => // redundant
      case _ =>
    }

    match nt {
      case -3 =>
      case -0 =>
      case 0 => // redundant
      case _ =>
    }
    
    match bv {
      case -3 => // error
      case -0 => // error
      case 0 =>
      case _ =>
    }

    match o {
      case -3 => // error
      case -0 => // error
      case 0 =>
      case _ =>
    }

    match r {
      case 2.18 =>
      case -2.18 =>
      case -0.0 =>
      case 0.0 => // redundant
      case _ =>
    }
  }
}

module RedundanCaseLiterals {
  newtype int8 = x | -128 <= x < 128

  method Tests(a: int, nt: int8, r: real) {
    match a {
      case -3 =>
      case -0 =>
      case 0 => // redundant
      case _ =>
    }

    match nt {
      case -3 =>
      case -0 =>
      case 0 => // redundant
      case _ =>
    }
    
    match r {
      case 2.18 =>
      case -2.18 =>
      case -0.0 =>
      case 0.0 => // redundant
      case _ =>
    }
  }
}
 */
