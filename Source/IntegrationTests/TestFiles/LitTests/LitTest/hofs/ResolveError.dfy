// RUN: %exits-with 2 %build "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
method ResolutionErrors() {
  var x;
  var g5 := x, y => (y, x);   // fail at resolution
  var g6 := x, (y => (y, x)); // fail at resolution
}

// cannot assign functions

class Apa {
  ghost function f() : int {
    0
  }
}

method Nope3() {
  var apa := new Apa;
  apa.f := () => 2;
}

method RequiresFail(f : int -> int)
  // ok
  requires f(0) == 0
  requires f.requires(0)
  requires f.reads(0) == {}

  // fail
  requires f(0) == true
  requires f(1,2) == 0
  requires f(true) == 0
  requires f.requires(true)
  requires f.requires(1) == 0
  requires f.requires(1,2)
  requires f.reads(true) == {}
  requires f.reads(1) == 0
  requires f.reads(1,2) == {}
{
}

method Bogus()
{
  var f;
  f := x reads 1 => x;
  f := x requires 1 => x;
}

predicate Bool()
{
  true
}

method Bla() {
  assert Bool;
}

method Pli<A,B>(f : A -> B) requires f != null
{
  var o : object;
  assert f != o;
}

method Underscores() {
  var u := _ => 0;
  var v := (_, _) => 0;
  var w := (_, _, _) => _;
}
}  // module Tests
module AritySituations {
  // In addition to testing type checking, these tests check that error messages
  //  print the types correctly
  function F(x: int, b: bool): real    // F:  (int,bool) -> real
  function G(pair: (int, bool)): real  // G:  ((int,bool)) -> real
  function V(): real                   // V:  () -> real
  function W(unit: ()): real           // W:  (()) -> real

  method M()
  {
    var f: (int, bool) -> real;
    var g: ((int, bool)) -> real;
    var h: (int, bool) -> real;
    f := F;
    g := G;
    h := G;  // error

    var f' := F;
    var g' := G;

    // (see method MF below) var s0 := P(F, 5);
    var s1 := P(G, (2, true));  // fine

    var v: () -> real;
    var w: (()) -> real;
    v := V;
    w := W;
    var v': () -> real := V;
    var w': (()) -> real := W;
    var w'': ((((((())))))) -> real := W;
    v := W;  // error
    w := V;  // error
  }

  method MF()
  {
    var s0 := P(F, 5);  // error: F takes 2 arguments, but P expect a function that takes 1
    var s1 := P(G, (2, true));  // fine
  }

  method P<T,U>(r: T -> U, x: T) returns (u: U)
    requires r.requires(x)
  {
    u := r(x);
  }
}

module Arrows {
  type MyInt = int

  function A(o: object, x: MyInt): nat
    requires x != 10
    reads o
  function B(o: object, x: MyInt): nat
    reads o
  function C(o: object, x: MyInt): nat
    requires x != 10
  function D(o: object, x: MyInt): nat

  method Test() returns (x: int) {
    x := A; // error
    x := B; // error
    x := C; // error
    x := D; // error

    x := (o: object, x: MyInt) requires x != 10 reads o => 2 as nat; // error
    x := (o: object, x: MyInt) reads o => 2 as nat; // error
    x := (o: object, x: MyInt) requires x != 10 => 2 as nat; // error
    x := (o: object, x: MyInt) => 2 as nat; // error
  }
}
