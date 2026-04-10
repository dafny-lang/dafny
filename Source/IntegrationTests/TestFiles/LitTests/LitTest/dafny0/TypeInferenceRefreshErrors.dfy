// RUN: %exits-with 2 %verify --type-system-refresh "%s" > "%t"
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
    var u;
    var w := !u; // fine: both u and w are inferred to have type bool (on account of advice)
  }
}

module Underspecification1 {
  class E<T> { }

  method M(obj: object) {
    var ee := obj as E; // error: type parameter of E is underspecified
    assert (obj as E) == (obj as E); // error: type parameter of E is underspecified
    assert (obj as E) == (obj as E<set>); // error: type parameter of set is underspecified
    assert (obj as E) == (obj as E<set<int>>);
  }


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
  type Synonym<X, Unused> = seq<X>

  method Underspecification() {
    // Regression: In the old type inference, the following line was not considered to be an error.
    var d: Synonym := [100, 101]; // error: type underspecified
  }
}

module Underspecification4 {
  type SubsetType<X, Unused> = s: seq<X> | |s| == 0

  method Underspecification() {
    // Regression: In the old type inference, the following would pass and would then crash the verifier:
    var e: SubsetType := [100, 101]; // error: type underspecified
  }
}

module Underspecification5 {
  type Synonym<A, Unused> = seq<A>

  method SM(x: Synonym<int, real>, y: seq<bool>) {
    var m: seq := y;

    var a := x;

    var b: Synonym := x; // error: type underspecified

    var k: seq := x;
    var y: Synonym := k; // error: type underspecified
  }
}

module DatatypeConstructorTypeArguments {
  datatype Color = White | Gray(int)
  datatype ParametricColor<X, Y> = Blue | Red(X) | Green(Y)

  method DatatypeValues() {
    var w := White<int>; // error (no hint, since the datatype doesn't take any type parameters)
    var b := Blue<int>; // error: with hint (since the datatype takes _some_ number of type parameters)
    var g := Gray<int>(2);
    var r := Red<int>(3);
  }
}

module RegressionTest {
  datatype R = R(int, int)

  method M() {
    var pair: (int, int) := (20, 30);
    match pair
    case R(x, y) => // error: tuple type does not have a constructor R
      // the following line causes a crash in the old type system, after reporting an error about the previous line
      print x + y;
  }
}

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

module NewMatchBehavior {
  /* Here are tests for a match where a case is given by a const.
   - For the first test, it used to be (that is, before the type system refresh) that this would spill out an unused
     local variable with that name (FIVE).
   - The second test checks what happens if the const case label is also given an explicit type.
     Previously, this would interpret "FIVE" as a const, and it would check that the type was correct.
     Now, the explicit type causes it to be interpreted as a bound variable.
   - The third test used to breeze through Dafny without any complaints, even though the type "int" makes no sense here.
     Now, a pattern with an explicit type is always interpreted as a bound variable.
   */

  const FIVE: int := 5

  method Five(x: int) {
    match x {
      case FIVE => assert x == 5;
      case _ =>
    }
    match x {
      case FIVE: int =>
        assert x == 5; // error: x may be anything, since FIVE is a bound variable
      case _ =>
    }
  }

  datatype Color = Blue | Green

  method Colors(c: Color) {
    match c
    case Blue: int => // error: because of the ": int", Blue is interpreted as a bound variable, and its type doesn't match that of "c"
  }
}

module MinusRegression {
  method M(s: seq<int>, b: bool) {
    var w := b - b; // error: - is not for bool
    var u := s - s; // error: - is not for seq
  }
}

module GreaterRegression {
  method M(s: seq<int>, b: bool) {
    var w := b > b; // error: > is not for bool
    var u := s >= s; // error: >= is not for seq
  }
}

module ArrayInitializer {
  method TestFunctionInit(n: nat, init: nat -> nat) {
    var a: array<bool> := new [n](init); // error: array<int> and array<bool> are incompatible
  }

  method TestDisplayInit(n: nat, init: nat -> nat) {
    var a: array<bool> := new [n] [23]; // error: array<int> and array<bool> are incompatible
  }
}

module EscapedStringLiterals {
  // Make sure that string literals given in the input are properly escaped before they are
  // displayed in error messages
  method Test() returns (u: int) {
    u := "x"; // error
    u := "{"; // error
    u := "{{"; // error
    u := "}"; // error
    u := "{0}"; // error

    u := 'x'; // error
    u := '{'; // error
  }
}

module VarianceErrorMessage {
  datatype Domain = Domain(subProgram: Program)

  datatype Program = Program(domains: seq<Domain>)

  // problem with covariance
  ghost function PRepr(p: Program): set<object> { // error: expects set<object>, gets set<set<...>>
    (set domain <- p.domains :: DRepr(domain))
  }

  ghost function DRepr(d: Domain): set<object> {
    PRepr(d.subProgram)
  }

  // problem with contravariance
  ghost function Func(): set<object> -> bool { // error: expects set<object> -> bool, gets set<set<...>> -> bool
    ss => SetSetProperty(ss)
  }

  ghost predicate SetSetProperty(ss: set<set<object>>)
}
