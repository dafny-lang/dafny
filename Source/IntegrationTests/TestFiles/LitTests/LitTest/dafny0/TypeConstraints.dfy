// RUN: %exits-with 2 %build --rprint:- --type-system-refresh=false --general-traits=legacy --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
module Tests {
class CC {
  var f: nat
  var g: int
  function F(): nat
  method M() {
    var a := f;  // nat
    var b := g;  // int
    var c := F();  // nat
    var w;  // nat
    var d := N(w);  // nat
  }
  method N(m: nat) returns (n: nat)
}

method ChainOfAssignments() returns (x: int, y: int, n: nat)
{
  var a;  // int
  var b := a;  // int
  var c := b;  // int
  x := c;
  y := x;

  var k, l, m;  // int, int, int
  k := l;
  l := m;
  m := x;

  var p, q;  // nat, nat
  p := q;
  q := n;
}
}  // module Tests
module HereAreErrors {
  method Error0() returns (x: int, z: bool)
  {
    var a, b, c;
    a, b := b, c;
    x := a;
    z := c;  // error (or on one of the lines above)
  }

  method Error1() returns (x: int, z: bool)
  {
    var a, b, c;
    a, b := b, c;
    z := c;
    x := a;  // error (or on one of the lines above)
  }

  method Error2() returns (x: int, z: bool)
  {
    var a, b, c;
    a, b := c, c;
    x := a;
    z := b;  // error (or on one of the lines above)
  }

  method Error3() returns (x: int, z: bool)
  {
    var a, b, c;
    c := a;
    c := b;

    x := a;
    z := b;  // error (or on one of the lines above)
  }

  newtype MyInt = x: int | true

  method Literals() returns (r: int, s: MyInt) {
    var a := 0;  // int
    var b := 0;  // MyInt
    r := a;
    s := b;
    a := b;  // error (or on the previous line)
    b := a;  // error (or on the previous two lines)
    r := s;  // error
    s := r;  // error
    var d, e;  // MyInt, MyInt
    d, e := e, b;
  }
}
module PL {
method PlainLiterals() {
  var x := 0;
  var r := 0.0;
}
}
module PlusTests {
  method Plus0() {
    var a, b, c;  // error (x2): underspecified type
    a := b + c;
  }
}
module PlusTests' {
  method Plus1() {
    var a;
    var b, c;
    a := b + c;  // error: invalid arguments to +
    a := true;
  }
  method Plus2() {
    var a, b, c;
    a := b + c;
    a := 0;
  }
  method Plus3() returns (r: int) {
    var a, b, c;
    a := b + c;
    a := r;
  }
  method Plus4() returns (r: int) {
    var a, b, c;
    a := b + c;
    r := a;
  }

  newtype MyInt = x: int | true
  method Plus5(y: MyInt) {
    var a, b, c;
    a := b + c;
    a := y;
  }
}

module MorePlusTests {
  newtype MyInt = x: int | true
  class C { }

  method Plusses(b: bool, i: int, j: MyInt, r: real) {
    var ii := i + i;
    var jj := j + j;
    var bb := b + b;  // error: bool is not plussable
    var rr := r + r;
    var s := {false};
    var ss := s + s;
    var m := multiset{false, false};
    var mm := m + m;
    var q := [false];
    var qq := q + q;
    var p := map[false := 17];
    var pp := p + p;
    var n: C := null;
    var nn := n + n;  // error: references types are not plussable
    var c := new C;
    var cc := c + c;  // error: class types are not plussable
  }
}

module References {
  class C extends K, M { }
  trait R extends object { }
  trait K extends object { }
  trait M extends object { }

  method M0() returns (c: C, r: R)
  {
    var o: object, k: K, m: M;
    o := o;
    c := c;
    r := r;
    k := c;
    m := c;

    o := c;
    o := r;
    o := k;
    o := m;
  }

  method M1() returns (c: C, r: R)
  {
    r := c;  // error
  }

  method M2() returns (c: C, r: R, o: object)
  {
    c := o as C;  // OK for type resolution, but must be proved
  }

  method M3() returns (c: C, r: R, o: object)
  {
    r := o as R;  // OK for type resolution, but must be proved
  }
}

module SimpleClassesAndTraits {
  class C extends K, M { }
  class D extends K, M { }
  trait R { }
  trait K extends object { var h: int }
  trait M { }

  method Infer(c: C, o: object, k: K, d: D) returns (k': K) {
    var delayme := c;  // object

    var x := c;  // C
    var yy := x.h;  // int

    delayme := o;

    var u := k;  // K
    var v := k;  // object
    v := o;
    v := c;
    var w := c;  // K
    w := k;

    var z := c;  // object
    z := o;

    var p := o;  // object
    var y;  // C
    var d: C := y;

    var n := null;   // object
    var n' := null;  // K (or object would be alright, too)
    n' := k;
    var n'' := null;  // K
    k' := n'';
  }
}

module TypeParameters {  // and abstract types
  type A
  type B
  type C<T,U>

  method M<G,H>(a: A, b: B, c0: C<int,bool>, g: G) returns (c1: C<real,real>, h: H)
  {
    var x := a;  // A
    var y, z;  // B, B
    y := z;
    z := b;

    var m, n;  // C<int,bool>, C<int,bool>
    n := m;
    m := c0;
    var k, l;  // C<real,real>, C<real,real>
    k := l;
    c1 := k;

    var g' := g;  // G
    var h', h'';  // H, H
    h' := h;
    h := h'';

    var r: C;  // type parameters inferred
    r := c1;
  }
}

module Datatypes {
  datatype Color = Red | Green | Blue

  method M() returns (c: Color) {
    var x := c;  // Color
    var y := x;  // Color
    var w, z;  // Color, Color
    w := z;
    c := w;
  }

  datatype Record<T,U> = Record(t: T, u: U)

  method P() returns (r: Record<int,bool>)
  {
    var a := r;  // Record<int,bool>
    var b, c;  // int, Record<int,bool>
    b := r.t;
    r := c;

    var s: Record;  // Record<int,real>
    var x, y := s.t, s.u;
    x := 5;
    y := 10.0;

    var t: Record;  // Record<bool,char>
    var tt: bool, uu: char;
    tt, uu := t.t, t.u;
  }
}

module TraitStuff {
  trait Part extends object {
    var id: int
  }
  trait Motorized { }
  class PartX extends Part {
  }
  class PartY extends Part, Motorized {
  }
  class PartZ extends Part, Motorized {
  }
  class Aggregate {
    ghost var Repr: set<object>
    var x: PartX
    var y: PartY
    var z: PartZ
    constructor ()
    {
      x := new PartX;
      y := new PartY;
      z := new PartZ;
      Repr := {this, x, y, z};  // set<object>
      new;
      var parts := {x, y};  // set<Part>
      var ooo := {y, z};  // set<object>  -- since super-traits are not unique
    }
  }
}

module OtherTraitsAndClasses {
  method Basics(x: int) returns (y: int)
  {
    var k := x;  // int
    var m;  // int
    y := m + m;
  }

  trait J { }
  trait K { }
  class C extends J { }
  class D extends J, K { }
  class E { }

  method Displays(c: C, d: D, e: E, j: J, k: K) {
    var s := {c, c};  // set<C>
    var t := {c, j};  // set<J>
    var t' := {j, c};  // set<J>
    var u := {c, d};  // set<J>
    var v := {c, e};  // set<object>
    var w := {k, c};  // set<object>
  }

  method G(c: C) {
    var s := {c};  // set<C>
    var t: set<C> := s;
    var u: set<object> := s;
  }

  method M() returns (r: nat)
  {
    var x, y, z, w;  // int, int, bool, int
    x := x + y;
    z := true;
    y := r;
    w := 0;
  }

  method Q0(s: set<char>) returns (t: set<char>) {
    var p := s + t;  // set<char>
  }

  method Q1<T>(s: set<MyClass>) returns (t: set<MyClass>) {
    var p := s + t;  // set<MyClass>
    var q: set<object> := s + t;
//    var r: set<T> := s + t;  // error
  }

  class MyClass { }

/******
  method P() {
    var w, u;  // int, unint8
    w := 0;
    u := 0;
    var v: uint8 := u;
  }

  newtype uint8 = x | 0 <= x < 256

  method Brackets(a: array<char>)
    requires a != null
  {
    var i;
    var ch := a[i];
    /*
    var s;  // s could be anything
    var n: nat := |s|;  // s could be a set, multiset, sequence, or map
    s := s + s;  // this excludes map
    s := s * s;  // this also excludes sequence
    var k := s[ch];  // and this excludes set, so s must be a multiset
    */
  }
******/
}

module LetPatterns {
  datatype MyDt = AAA(x: int) | BBB(y: int)

  ghost function M(m: MyDt): int
    requires m.AAA?
  {
    var AAA(u) := m;  // u: int
    u
  }

  method P()
  {
    var v;  // v: int
    var m;  // m: MyDt
    var w := v + var AAA(u) := m; u;  // m may not be an AAA, but that's checked by the verifier
  }

  method Q(x: int, r: real)
  {
    var o;  // real
    var u := (x, o);  // (int,real)
    o := r;
  }
}

module Arrays_and_SubsetTypes {
  method M()
  {
    var a: array<nat>;
    var b: array<int>;
    if * {
      a := new nat[100];
      b := new nat[100]; // ERROR
    } else if * {
      a := new int[100]; // ERROR
      b := new int[100];
    } else if * {
      a := b;  // ERROR
    } else if * {
      b := a;  // ERROR
    } else if * {
      var n := new nat[100];  // array<nat>
      if * {
        a := n;
      } else {
        b := n; // A verification error
      }
    }
  }
}

module Arrays_and_SubsetTypesOK {
  method M()
  { // Type-wise, all of the following are allowed (but the verifier will complain):
    var a: array<nat>;
    var b: array<int>;
    if * {
      a := new nat[100];
      b := new nat[100]; // Error
    } else if * {
      a := new int[100]; // Error
      b := new int[100];
    } else if * {
      a := b;            // Error
    } else if * {
      b := a;            // Error
    } else if * {
      var n := new nat[100];  // array<nat>
      if * {
        a := n;
      } else {
        b := n;
      }
    }
  }
}

module TypeArgumentPrintTests {
  trait Tr<X> extends object { }

  class Cl<Y> extends Tr<Y> {
    lemma M() {
      var u: Tr := this;  // should print as "var u: Tr<Y> := this;"
      var v: Tr<Y> := this;  // should print as "var v: Tr<Y> := this;"
    }
  }

  // -----
  class A<X> {
    static function F(x: X): int { 15 }
  }

  class B<Y> {
    function H(y: Y, b: bool): int {
      if b then
        A.F(y)  // should print as A<Y>.F(y)
      else
        A<Y>.F(y)  // should print as A<Y>.F(y)
    }
  }
}

module PrettyPrintingBindingPowers {
  newtype MyInt = u: int | u != 193

  method M(m: map<int, real>, n: map<int, real>, a: set<int>, b: set<int>, c: set<int>) returns (r: map<int, real>)
  {
    r := m - b - c;
    r := m - b + n;
    r := (m - b) + n;  // unnecessary parentheses
    r := m - (b + c);
    r := m + n - (b + c);
    r := m + (n - (b + c));
    r := m + (n - b) - c;
    r := m + (m + n) + m;
    r := (((m + m) + n) + m);  // unnecessary parentheses
  }

  method P() returns (x: int, u: MyInt, s: set<int>, e: seq<int>, m: map<int, int>)
  {
    x := x + (x + x);  // unnecessary parentheses
    u := u + (u + u);
    s := s + (s + s);
    e := e + (e + e);
    m := m + (m + m);
  }
}

module SameSCC {
  // all of these should be in the same SCC
  type G0 = G1
  type G1 = G2
  type G2 = G3<int>
  type G3<X> = (X, G4)
  type G4 = G5
  datatype G5 = G5(G6)
  codatatype G6 = G6(array<G0>)
}

module UnderspecifiedTypeConversions0 {
  class Cell<X> { }
  type UCell<U, V> = Cell<U>

  method M(c: Cell<int>) {
    if c is UCell { // error: type is underspecified
      print "yes";
    }
  }

  method N(c: object) {
    if c is Cell { // error: type is underspecified
      print "yes";
    }
  }
}

module UnderspecifiedTypeConversions1 {
  class Cell<X> { }
  type UCell<U, V> = Cell<U>

  method M(c: Cell<int>) {
    var d: Cell<int>;
    d := c as UCell; // error: type is underspecified
  }

  method N(c: object) {
    var d: object;
    d := c as Cell; // error: type is underspecified
  }
}
