// RUN: %exits-with 2 %dafny  /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  const two:int := 2.5   // error: type does not match
}

module A' {
  const one:int := 1
  const three:int := 3
  const four:int := three + one
  const five:int := six - one  // error: cycle between five, six
  const six: int := five + one
}

module B {  // non-static const's
  class Class {
    const a: int := 10
    static function method G(): int
    {
      a  // error: "a" is an instance field, but G() is static
    }
  }
}

module C {  // ghost const's
  ghost const x: int := 10
  class Class {
    ghost const y: int := 20
    function method F(): int
    {
      x +  // error: "x" is ghost
      y  // error: "y" is ghost
    }
  }
}

module D {  // const's with inferred types
  const pi := 3.14
  const ten := 10  // this type should be "int", not "SmallInt"

  newtype SmallInt = x | 0 <= x < 100
  method M() returns (sm: SmallInt) {
    sm := ten;  // error: "int" is not assignable to "Smallint"
  }

  method R() returns (r: real) {
    r := pi;
  }
}

// ---------- traits --------------------

module E {
  newtype Six = x | 6 <= x witness 6

  trait Trait {
    const x0: Six
    const x1: Six := 7
    const x2: Six
    const x3: Six := 8

    static const y: Six := 10
  }

  class Class extends Trait {
    const x0: Six  // error: not allowed to declare const
    const x1: Six := 7  // error: not allowed to declare const
    const x2: Six  // error: not allowed to declare const
    const x3: Six  // error: not allowed to declare const

    method Test() {
      print x0, " ", x1, " ", x2, "\n";
      print y, "\n";
    }
  }
}

// ---------- instanced-based initialization --------

module F {
  newtype Six = x | 6 <= x witness 6

  trait Trait {
    const x0: Six
    const x1: Six := 7
  }

  class InstanceInit extends Trait {
    const y2: Six
    const y3: Six := 12

    constructor (u: int)
      requires 10 <= u
    {
      x0 := 80;
      x1 := 100;  // error: cannot set a const whose declaration has an initial value
      y2 := 77 + y3;
      y3 := 110;  // error: cannot set a const whose declaration has an initial value
      new;
      x0, x1, y2, y3 := 50, 50, 50, 50;  // error (x4): cannot set const's after "new;"
    }
  }
}

// ---------- cyclic dependencies --------

module G {
  const a: int := c  // error: cyclic dependency between a, b, and c
  const b := G(a)
  const c := F(b)
  function method G(x: int): int { x + 2 }
  function method F(x: int): int { 2 * x }

  ghost const x: int := H(10)  // error: cyclic dependency between x and H
  function H(y: int): int { y + x }

  function H'(y: int): int { y + x' }
  ghost const x': int := H'(10)  // error: cyclic dependency between x' and H'
}

module H { // self cycles are checked earlier
  const ur: int := ur  // error: cycle
}

module I {
  newtype A = x: int | F(x)  // error: recursive dependency: A, F
  function F(x: int): bool
  {
    var b: A :| true;
    b == b
  }
}

module J {
  newtype A = x: int | F(x)  // error: recursive dependency: A, F, B
  function F(x: int): bool
  {
    var b: B :| true;
    b == b
  }
  type B = a:A | true  // (note, no duplicate error message here)
}

module K {
  newtype A = x: int | var l := F(x); true  // error: recursive dependency: A, F, B
  function F(x: int): bool
  {
    var b: B := 6;
    b == b
  }
  type B = A
}

module L {
  newtype A = x: int | F(x)  // error: recursive dependency: A, F, B
  function F(x: int): bool
  {
    var b: B :| true;
    b == b
  }
  datatype B = Ctor(A)
}

module M {
  newtype A = x: int | F(x)  // error: recursive dependency: A, F, B, C
  function F(x: int): bool
  {
    var b: B :| true;
    b == b
  }
  datatype B = Ctor(C, B) | Nil
  type C = A
}

module N {
  predicate Cmp(x: int, y: int) { x < y }

  // here comes a long recursive definition of the constraints
  newtype A = x: int | Cmp(x, b)  // error: recursive dependency: A, b, MakeC, C, D, E, f, G, H, I, j, K, L, M, n, MakeA
  const b := var c := MakeC(); if c == c then 5 else 7
  function method MakeC(): C
  type C = D
  datatype D = Ctor(E)
  type E = x: int | f(x)
  predicate f(x: int)
  {
    var g: G :| true;  // function -> codatatype
    x % 3 == 0
  }
  codatatype G = CoCtor(H)
  type H = I
  type I = x: int | j(x)
  predicate j(x: int)
  {
    var k: (bool, K) :| true;
    x % 5 == 0
  }
  type K = (L, (), int)
  datatype L = LCtor((M, real))
  type M = x: int | x < n
  const n := var o: (bv5, A) := (2, MakeA()); 300
  function method MakeA(): A
}

module O {
  type A = (B, C)  // error: cyclic types
  type B = (C, D)
  type C = (D, A)
  type D = (A, B)
}

module P {
  type G
  const g: G  // error: unknown how to initialize a "G"
}

abstract module Q {
  type G
  const g: G  // fine, because, unlike module P, Q is an abstract module (but see non-abstract module R0 below)
  const k: int
}

module R0 refines Q {
  // error: unknown how to initialize "g", which is a "G"
}

module R1 refines Q {
  type G = real  // specify G
  // now, it is known how to initialize "g", so inherited definition of "g" is fine
}

module R2 refines Q {
  type G = real  // specify G
  const g: G := 3.14  // specify g, all good
  const k: int := 100
}

module S {
  class MyClass {
    var a: int
    const b: int
    static const u: real
    const v: real
  }
  const k: int
  const l: int
  const m: int := 15
  const x: int := 200
  const y := 800
  const z: int
}

module T refines S {
  class MyClass ... {
    const a: int  // error: cannot change a "var" to a "const"
    var b: int  // error: cannot change a "const" to a "var"
    const u: real  // error: cannot change from static to non-static
    static const v: real  // error: cannot change from non-static to static
  }
  const k := 100  // it's okay to omit the type of "k"
  type MyInt = int
  const l: MyInt := 100  // error: type must be syntactically the same as in "S"
  const m: int := 17  // error: cannot re-supply a RHS
  ghost const x: int  // this ghostified field inherits the RHS from above
  const y: int  // error: there must be more of a change to allow a re-declaration
  const z := 2.7  // error: bad type for the RHS
}

// ---------- assign-such-that --------

module AssignSuchThat {
  method Duplicate() {
    var x: int;
    x, x :| true;  // error: duplicate LHS
  }

  class MyClass {
    const c: int

    method M() {
      c :| assume true;  // error: c is not mutable
    }
  }
}
