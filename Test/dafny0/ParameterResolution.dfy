// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Actuals {
  function method F(x: int, y: int, z: int): int

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
    function method Generic0<X>(): int
    function method Generic1<X>(p: X): int

    method T0(x: int := u + this.u + v + this.v, y: int := if this != null then 0 else 2)
    function method T1(x: int := u + this.u + v + this.v, y: int := if this != null then 0 else 2): int
    static method T2(x: int := if this != null then 0 else 2) // error: 'this' is not in scope
    static function T3(x: int := if this != null then 0 else 2): int // error: 'this' is not in scope
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
  function method C(n: nat := C()): nat // error: default-value expression has infinite expansion

  function F(m: nat := G(), n: nat := H()): int // error (3 cycles): default-value expression has infinite expansion
  function G(m: nat := 10, n: nat := F()): int
  function H(m: nat := F()): int

  // The following two declarations can cause the Resolver to produce infinite expressions (or loop forever), if not handled carefully
  function method InfiniteLoopFunction(n: nat := InfiniteLoopFunction()): nat // error: InfiniteLoopFunction used in its own default value
  lemma InfiniteLoopLemma(n: nat := (InfiniteLoopLemma(); 3)) // error: InfiniteLoopLemma used in its own default value
}

module Modes {
  method G0(x: int := y, y: int := 0)
  method G1(x: int := y, ghost y: int := 0) // error: cannot assign ghost -> compiled
  method G2(ghost x: int := y, y: int := 0)
  method G3(ghost x: int := y, ghost y: int := 0)
  ghost method G4(x: int := y, y: int := 0)

  function method CompiledFunction(): int
  function GhostFunction(): int
  method H0(x: int := CompiledFunction(), y: int := GhostFunction()) // error: y is assigned a ghost
  method H1(x: int := CompiledFunction(), ghost y: int := GhostFunction())
  method H2(ghost x: int := CompiledFunction(), y: int := GhostFunction()) // error: y is assigned a ghost
  method H3(ghost x: int := CompiledFunction(), ghost y: int := GhostFunction())
  ghost method H4(x: int := CompiledFunction(), y: int := GhostFunction())

  function method FG(ghost u: int): int
  function method FC(u: int): int
  method          MG0(      x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x))
  method          MG1(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)) // error: call to FC passes in a ghost expression
  function method MG2(      x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)): int
  function method MG3(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)): int // error: call to FC passes in a ghost expression
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
    function method M(x: int := 5): int
    function method N(x: int := 5): int
    function method O(x: int): int
  }
  class Class extends Trait {
    function method M(x: int := 6): int { 2 * x } // it's fine to change default-value expressions
    function method N(x: int): int { 2 * x } // it's fine to drop a default-value expression
    function method O(x: int := 6): int { 2 * x } // it's fine to add a default-value expression
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
  function method M(x: int := 5): int
  function method N(x: int := 5): int
  function method O(x: int): int

  method Test0() {
    // the default value that gets used depends on the module where the call is
    assert M() == 10;
    assert N() == 10;
    assert O() == 10; // error (x2 -- the second time in RefinementB): needs a parameter
  }

  function method FF(x: int := 5): (r: int)
    ensures r == x
  method MM(x: int := 5) returns (r: int)
    ensures r == x
  lemma Lemma0()
    ensures FF() == 5
  {
  }
}

module RefinementB refines RefinementA {
  function method M(x: int := 6): int { 2 * x } // error: refinement module cannot indicate default value on refined parameter
  function method N(x: int): int { 2 * x }
  function method O(x: int := 6): int { 2 * x } // error: refinement module cannot indicate default value on refined parameter

  method Test1() {
    // the default value that gets used depends on the module where the call is
    assert M() == 12;
    assert N() == 12;
    assert O() == 12; // error: needs a parameter
  }

  function method FF(x: int := 6): int { x } // error: refinement module cannot indicate default value on refined parameter
  function method F'(x: int := 6): int { x }
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
  function method F<X>(): int

  method P(y: int := F()) { // error: type parameter X not determined
    var f := F(); // error: type parameter X not determined
  }
  function G(y: int := F()): int // error: type parameter X not determined
  iterator Iter(y: int := F()) // error: type parameter X not determined (the error gets reported twice)
  datatype Record = Record(y: int := F()) // error: type parameter X not determined
}

module RequiresBeforeOptional {
  datatype Color = Blue(x: int := y, y: int) // error: required parameters must precede optional parameters
  iterator Iter(x: int := y, y: int) // error: required parameters must precede optional parameters (reported twice)
  lemma Lemma(x: int := y, y: int) // error: required parameters must precede optional parameters
  least predicate Least(x: int := y, y: int) // error: required parameters must precede optional parameters
}
