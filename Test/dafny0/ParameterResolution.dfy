// RUN: %exits-with 2 %dafny "%s" /dprint:"%t.dprint" > "%t"
// RUN: %diff "%s.expect" "%t"

module Actuals {
  function F(x: int, y: int, z: int): int

  method M0() {
    var a0 := F(2, 3, 5);
    var a1 := F(2, y := 3, z := 5);
    var a2 := F(2, z := 5, y := 3);
    var a3 := F(x := 2, y := 3, z := 5);
    var a4 := F(y := 3, x := 2, z := 5);
    assert a0 == a1 == a2 == a3 == a4;
  }

  method M1() {
    var a0 := F(2, 3); // error: too few arguments
    var a1 := F(2, 3, 5, 7); // error: too many arguments
    var a2 := F(2, y := 3, y := 5); // error: repeated parameter y (and no z)
    var a3 := F(2, x := 5, y := 3); // error: repeated parameter x (and no z)
    var a4 := F(2, y := 3, 5); // error: positional argument follows named argument
  }

  datatype Record = Record(a: int, bool, c: real)

  method M2() {
    var a0 := F(2, 3, xyz := 5); // error: no parameter of F is called 'xyz'
    var r0 := Record(2, true, 3.9);
    var r1 := Record(2, true, c := 3.9);
    var r2 := Record(2, c := 3.9); // error: too few arguments
    var r3 := Record(2, c := 3.9, a := 2); // error: 'a' already given positionally
  }
}

module Formals {
  class C<GG> {
    var u: int
    const v: int

    method M0(x: int := 100, y: int := 200)
    method M1(x: int := true) // error: expected int, got bool
    method M2<X>(x: X, y: X := x)
    method M3(x: ORDINAL := 5)
    method M4(x: int := Generic0<GG>(), y: int := 0)
    method M5(x: int := Generic1(y), y: int := 0)
    function Generic0<X>(): int
    function Generic1<X>(p: X): int

    method T0(x: int := u + this.u + v + this.v, y: int := if this != null then 0 else 2)
    function T1(x: int := u + this.u + v + this.v, y: int := if this != null then 0 else 2): int
    static method T2(x: int := if this != null then 0 else 2) // error: 'this' is not in scope
    static ghost function T3(x: int := if this != null then 0 else 2): int // error: 'this' is not in scope
    static method T4(x: int := u + this.u + v + this.v) // error (x4): 'this' is not in scope
    constructor T5(x: int := this.u) // error: 'this' is not in scope for constructor
  }

  datatype Datatype0 = Ctor0(a: int := 6) | Ctor1(a: int := 7) | Ctor2(a: int) // the 'a' destructor is allowed a different default value for each constructor
  datatype Datatype1 = Ctor0(a: int := b) | Ctor1(b: int) // error: 'b' is not in scope

  method C0(x: int := x + 3) // error: cycle among parameter default-value dependencies: x -> x
  method C1(x: int := y, y: int := 0, z: int := y)
  method C2(x: int := y, y: int := z, z: int := x) // error: cycle among parameter default-value dependencies: x -> y -> z -> x
}

module InfiniteExpansion {
  function C(n: nat := C()): nat // error: default-value expression has infinite expansion

  ghost function F(m: nat := G(), n: nat := H()): int // error (3 cycles): default-value expression has infinite expansion
  ghost function G(m: nat := 10, n: nat := F()): int
  ghost function H(m: nat := F()): int

  // The following two declarations can cause the Resolver to produce infinite expressions (or loop forever), if not handled carefully
  function InfiniteLoopFunction(n: nat := InfiniteLoopFunction()): nat // error: InfiniteLoopFunction used in its own default value
  lemma InfiniteLoopLemma(n: nat := (InfiniteLoopLemma(); 3)) // error: InfiniteLoopLemma used in its own default value
}

module Modes {
  method G0(x: int := y, y: int := 0)
  method G1(x: int := y, ghost y: int := 0) // error: cannot assign ghost -> compiled
  method G2(ghost x: int := y, y: int := 0)
  method G3(ghost x: int := y, ghost y: int := 0)
  ghost method G4(x: int := y, y: int := 0)

  function CompiledFunction(): int
  ghost function GhostFunction(): int
  method H0(x: int := CompiledFunction(), y: int := GhostFunction()) // error: y is assigned a ghost
  method H1(x: int := CompiledFunction(), ghost y: int := GhostFunction())
  method H2(ghost x: int := CompiledFunction(), y: int := GhostFunction()) // error: y is assigned a ghost
  method H3(ghost x: int := CompiledFunction(), ghost y: int := GhostFunction())
  ghost method H4(x: int := CompiledFunction(), y: int := GhostFunction())

  function FG(ghost u: int): int
  function FC(u: int): int
  method          MG0(      x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x))
  method          MG1(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)) // error: call to FC passes in a ghost expression
  function MG2(      x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)): int
  function MG3(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)): int // error: call to FC passes in a ghost expression
  datatype MG4 =  MG4(      x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x))
  datatype MG5 =  MG5(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)) // error: call to FC passes in a ghost expression
  iterator        MG6(      x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x))
  iterator        MG7(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)) // error: call to FC passes in a ghost expression

  iterator Iter0(x: int := y, y: int := 0) { }
  iterator Iter1(x: int := y, ghost y: int := 0) { } // error: cannot assign ghost to non-ghost
  iterator Iter2(ghost x: int := y, y: int := 0) { }
  iterator Iter3(ghost x: int := y, ghost y: int := 0) { }

  datatype Dt0 = Make(x: int := y, y: int := 0)
  datatype Dt1 = Make(x: int := y, ghost y: int := 0) // error: cannot assign ghost -> compiled
  datatype Dt2 = Make(ghost x: int := y, y: int := 0)
  datatype Dt3 = Make(ghost x: int := y, ghost y: int := 0)
}

module Overriding {
  trait Trait {
    function M(x: int := 5): int
    function N(x: int := 5): int
    function O(x: int): int
  }
  class Class extends Trait {
    function M(x: int := 6): int { 2 * x } // it's fine to change default-value expressions
    function N(x: int): int { 2 * x } // it's fine to drop a default-value expression
    function O(x: int := 6): int { 2 * x } // it's fine to add a default-value expression
  }
  method TestOverriding(c: Class) {
    assert c.M() == 12;
    assert c.N() == 12; // error: needs a parameter
    assert c.O() == 12;

    var t: Trait := c;
    assert t.M() == 10;
    assert t.N() == 10;
    assert t.O() == 10; // error: needs a parameter
  }

}

module RefinementA {
  function M(x: int := 5): int
  function N(x: int := 5): int
  function O(x: int): int

  method Test0() {
    // the default value that gets used depends on the module where the call is
    assert M() == 10;
    assert N() == 10;
    assert O() == 10; // error (x2 -- the second time in RefinementB): needs a parameter
  }

  function FF(x: int := 5): (r: int)
    ensures r == x
  method MM(x: int := 5) returns (r: int)
    ensures r == x
  lemma Lemma0()
    ensures FF() == 5
  {
  }
}

module RefinementB refines RefinementA {
  function M(x: int := 6): int { 2 * x } // error: refinement module cannot indicate default value on refined parameter
  function N(x: int): int { 2 * x }
  function O(x: int := 6): int { 2 * x } // error: refinement module cannot indicate default value on refined parameter

  method Test1() {
    // the default value that gets used depends on the module where the call is
    assert M() == 12;
    assert N() == 12;
    assert O() == 12; // error: needs a parameter
  }

  function FF(x: int := 6): int { x } // error: refinement module cannot indicate default value on refined parameter
  function F'(x: int := 6): int { x }
  method MM(x: int := 6) returns (r: int) // error: refinement module cannot indicate default value on refined parameter
  {
    r := x;
  }
  method M'(x: int := 6) returns (r: int)
    ensures r == x
  {
    r := x;
  }

  lemma Lemma1()
    ensures FF() == 6
  {
  }
}

module TypesAreDetermined {
  function F<X>(): int

  method P(y: int := F()) { // error: type parameter X not determined
    var f := F(); // error: type parameter X not determined
  }
  ghost function G(y: int := F()): int // error: type parameter X not determined
  iterator Iter(y: int := F()) // error: type parameter X not determined (the error gets reported twice)
  datatype Record = Record(y: int := F()) // error: type parameter X not determined
}

module RequiredBeforeOptional {
  datatype Color = Blue(x: int := y, y: int)
  iterator Iter(x: int := y, y: int)
  lemma Lemma(x: int := y, y: int)
  least predicate Least(x: int := y, y: int)
}

module TwoState {
  class C {
    var x: int
    method M(u: int := old(x)) // error: old not allowed in this context
    twostate lemma N(u: int := old(x))
    function F(u: int := old(x)): int // error: old not allowed in this context
    twostate function G(u: int := old(x)): int
  }
  iterator Iter(c: C, u: int := old(c.x)) // error: old not allowed in this context
  datatype D = D(c: C, u: int := old(c.x)) // error: old not allowed in this context
}

module NullaryDatatypeConstructors0 {
  datatype Ax = Nothing()
  datatype Bx = Nothing(x: int := 500)

  method M() {
    var n0 := Nothing; // error: ambiguous
    var n1 := Nothing(); // error: ambiguous
    var n2 := Nothing(2); // error: ambiguous
  }

  datatype Dx = Create()
  datatype Ex = Create(x: int := 500)

  method P() {
    var d0 := Dx.Create();
    var d1 := Dx.Create; // fine without parentheses
    var e0 := Ex.Create(); // gets default parameter
    var e1 := Ex.Create; // this, too, gets the default parameter
    var e2 := Ex.Create(2); // gets given parameter
    var e3 := Ex.Create(2, 3); // error: too many arguments
  }
}

module MissingParameters {
  method M(a: int, b: int, c: int := 0, d: int := 2, e: int := 4)
  method Caller() {
    M(c := 2); // error (x2): missing parameters ("a" and "b")
    M(c := 2, e := 7); // error (x2): missing parameters ("a" and "b")
  }
}

module DuplicateFormal {
  method Bad(x: int, x: int) // error: duplicate formal name
  method GoodCallerOfBad() {
    Bad(2, 3);
  }
}

module MoreSimpleTests {
  method M(x: int := x) // error: cycle among parameters and their default values
  least predicate P[nat](x: int := _k) // error: _k not allowed
  least lemma L(x: int := _k) // error: _k not allowed
}

module NameOnlyParameters {
  class C {
    var x: int
    constructor (a: int, b: int := 8, nameonly c: int := 9)
    constructor Init(a: int, b: int := 8, nameonly nameonly ghost nameonly c: int := 9)
    constructor Create(a: int, nameonly b: int := 8, c: int := 9)
    constructor Make(a: int, nameonly b: int := 8, c: int := 9)
    method M(a: int, nameonly b: int, c: int := 100)
    method P(a: int, nameonly b: int, c: int := 100)
    twostate lemma N(a: int, nameonly b: int, c: int := 100)
    function F(a: int, nameonly b: int, c: int := 100): int
    least predicate LP(a: int, nameonly b: int, c: int := 100)
    static greatest predicate GP(a: int, nameonly b: int := 75, c: int := 100)
  }
  iterator Iter(nameonly u: int, x: int) // error (x2, because of the desugaring of iterators): x is effectively nameonly, but not declared as such
  datatype D =
    | DD(a: int, nameonly b: int)
    | DE(int, 0: int, real, nameonly 1: int, c: int) // error: c is effective nameonly, but not declared as such
    | DF(800: int, nameonly 900: int, 9_0_0: int := 100)
  datatype E =
    | E0(a: int, b: int := 6, int) // error: there is no way for the default value of 'b' to be used
    | E1(a: int, nameonly b: int := 6, u: int) // u is effectively nameonly
    | E2(a: int, nameonly b: int, int) // error: after a 'nameonly' parameter, all remaining parameters must be nameonly or have a default value

  method Test() {
    var c: C;
    c := new C(2, 3, 4); // error: c is nameonly
    c := new C(2, 3, c := 4);
    c := new C(2, b := 3, c := 4);
    c := new C(2, c := 4, b := 3);
    c := new C(a := 2, c := 4, b := 3);
    c := new C(c := 4, b := 3, a := 2);

    c := new C.Init(2, 3, 4); // error: c is nameonly
    c := new C.Init(2, c := 4);
    c := new C.Init(2);

    c := new C.Create(2, b := 20, 200); // error: positional argument follows named argument
    c := new C.Create(b := 20, a := 2);
    c := new C.Create(c := 200, b := 20, a := 2);

    c := new C.Make(2, 3, 4); // error: b is nameonly
    c := new C.Make(2, b := 3, c := 4);
    c := new C.Make(b := 3, c := 4, a := 2);
    c := new C.Make(b := 3, unknown := 4, a := 2); // error: no parameter named 'unknown'
    c := new C.Make(b := 900, a := 901);

    c.M(2, b := 3);
    c.M(2, b := 3, 102); // error: positional argument follows named argument
    c.M(2, 102, b := 3); // error (x2): b is nameonly, b is duplicated
    c.M(2, b := 102, b := 3); // error: b is duplicated
    c.P(b := 2, a := 0);
    c.P(a := 0, b := 2);
    c.P(0, b := 2);
    c.P(0, b := 2, c := 5);
    c.N(b := 3, a := 2);
    c.N(2, b := 3, c := 4);

    var x;
    x := c.F(2, 3, 4); // error: b is nameonly
    x := c.F(a := 2, b := 3, c := 4);

    assert c.LP(c := 20, b := 7, a := 2);
    assert c.LP(2, b := 7);
    assert c.LP(2); // error: parameter 'b' has no value
    assert c.LP(2, c := 4); // error: parameter 'b' has no value
    assert c.LP(2, b := 4);
    assert c.GP(2, c := 4);
    assert C.GP(2, c := 4, b := 12);
    assert C.GP(2, c := 4, b := 12, a := 2); // error: parameter 'a' given twice

    var iter;
    iter := new Iter(3, 2); // error: u is nameonly
    iter := new Iter(u := 3, 3); // error (x2): positional argument not allowed to follow named arguments
    iter := new Iter(u := 3, x := 3);
    iter := new Iter(x := 3, u := 3);
    iter := new Iter(x := 3, u := 3, x := 3); // error: parameter 'x' given twice

    var d;
    d := DD(a, b := 3); // error: unidentified 'a'
    d := DD(a := 0, b := 3);
    d := DD(b := 3, a := 0);
    d := DD(0, b := 3);

    d := DE(0, 1, 0.0, 1 := 8, c := 9);
    d := DE(0, 1, 0.0, c := 9, 1 := 8);

    d := DF(2, 3, 4); // error: 900 is a nameonly
    d := DF(2, 900 := 3, 9_0_0 := 4);
    d := DF(2, 900 := 3);
    d := DF(900 := 3, 9_0_0 := 4, 800 := 2);
    d := DF(2, 0900 := 3, 9_0_0 := 4); // error (x2): no parameter is named '0900'; no argument passed for parameter '900'
    d := DF(2, 900 := 3, 90_0 := 4); // error: no parameter is named '90_0'
  }

  // Issue 3859
  datatype Foo = Foo(nameonly bar: string := "", nameonly baz: string, qux: int := 8)
  function FooF(nameonly bar: string := "", nameonly baz: string, qux: int := 8): int
  method FooM(nameonly bar: string := "", nameonly baz: string, qux: int := 8)

  datatype XFoo = XFoo(bar: string := "", nameonly baz: string, qux: int := 8)
  function XFooF(bar: string := "", nameonly baz: string, qux: int := 8): int
  method XFooM(bar: string := "", nameonly baz: string, qux: int := 8)

  datatype YFoo = YFoo(bar: string := "", nameonly baz: string, qux: int := 8, ohno: int, quux: real := 2.0) // error: onho is effectively nameonly, but not declared as such
  function YFooF(bar: string := "", nameonly baz: string, qux: int := 8, ohno: int, quux: real := 2.0): int // error: onho is effectively nameonly, but not declared as such
  method YFooM(bar: string := "", nameonly baz: string, qux: int := 8, ohno: int, quux: real := 2.0) // error: onho is effectively nameonly, but not declared as such

  method FooUse() {
    var f := Foo(baz := "yeah");
    f := Foo(baz := "yeah", bar := "fun");
    f := Foo(bar := "fun", baz := "yeah", qux := 10);
    f := Foo(qux := 10, baz := "yeah");
    f := Foo(); // error: baz is missing
    var y := YFoo(baz := "a", ohno := 21);
  }
}
