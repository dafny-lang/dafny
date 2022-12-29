// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Actuals {
  datatype List<T> = Nil | Cons(T, tail: List<T> := Nil)

  method M(a: int, b: int) returns (r: int)
    ensures r == a + 2 * b
  {
    r := a + 2 * b;
  }

  function method F(a: int, b: int, c: int): int
  {
    a + 2 * b + 3 * c
  }

  class Cell<U> {
    var value: U
    constructor (u: U)
      ensures value == u
    {
      value := u;
    }
  }

  iterator Iter(a: int, b: int) yields (z: int) {
  }

  method ParsingActualBindings() {
    var xs0 := Cons(5, tail := Cons(7, Nil));
    var tuple0 := (1 := 10, 0 := 300);
    var r0 := M(100, b := 60);
    var x0 := F(200, c := 20, b := 10);
    var c0 := new Cell(u := 75);
    var iter0 := new Iter(10, b := 20);

    var xs1 := Cons(5, Cons(7, Nil));
    var tuple1 := (300, 10);
    var r1 := M(100, 60);
    var x1 := F(200, 10, 20);
    var c1 := new Cell(75);
    var iter1 := new Iter(10, 20);

    assert xs0 == xs1;
    assert tuple0 == tuple1;
    assert r0 == r1;
    assert x0 == x1;
    assert c0.value == c1.value;
    assert iter0.a == iter1.a && iter0.b == iter1.b;
  }
}

module Termination {
  function method R(n: nat := R(0)): nat { n } // error: default value cannot make recursive call
}

module TwoState {
  class C { }

  twostate predicate P0(a: C, b: C := a)
  twostate predicate P1(a: C, new b: C := a)
  twostate predicate P2(new a: C, b: C := a) // error: 'b' needs to have been allocated already in the old state
  twostate predicate P3(new a: C, new b: C := a)
  twostate lemma L0(a: C, b: C := a)
  twostate lemma L1(a: C, new b: C := a)
  twostate lemma L2(new a: C, b: C := a) // error: 'b' needs to have been allocated already in the old state
  twostate lemma L3(new a: C, new b: C := a)
}

module A {
  function method F(x: int := 5): (r: int)
    ensures r == x
  method M(x: int := 5) returns (r: int)
    ensures r == x

  lemma Lemma0()
    ensures F() == 5
  {
  }
}

module B refines A {
  function method F(x: int): int { x }
  method M(x: int) returns (r: int) { r := x; }

  function method F'(x: int := 6): int { x }
  method M'(x: int := 6) returns (r: int) ensures r == x { r := x; }

  lemma Lemma1()
    ensures F() == 6
  { // error: postcondition violation
  }

  method TestLemmas() {
    var y := F();
    if * {
      Lemma0();
      assert y == 5;
    } else if * {
      Lemma0();
      assert y == 6; // error
    } else if * {
      Lemma1();
      assert F() == 5 && F() == 6; // fine, since F() promises one and Lemma1() the other
    } else if * {
      assert F() == 5;
      var r := M();
      assert r == 5;
      assert r == 7; // error
    } else {
      assert F'() == 6;
      var r := M'();
      assert r == 6;
    }
  }
}

module Wellformedness {
  class C {
    var u: int
    const v: int

    function T0(x: int := this.u): int // error: insufficient reads clause

    function T1(x: int := this.v): int

    function T2(c: C, x: int := c.u): int
      reads c

    function T3(c: C, x: int := c.u): int // error: insufficient reads clause
      requires c == this
      reads this

    function T4(x: int := 10, z: int := 10 / x): int // error: division by zero

    function T5(x: int, z: int := 10 / x): int // error: division by zero (despite precondition)
      requires x == 10

    function T6(x: int := 3 / y, y: int := 10): int // error: division by zero (despite precondition)
      requires y == 10

    function T7(x: int := 3, y: int := 10): int
      requires y == 8
      requires 1 / x == 2000 // error: division by zero
  }

  method M0(x: int := 8, y: int := 10 / x) // error: division by zero

  method M1(x: int, z: int := 10 / x) // error: division by zero (despite precondition)
    requires x == 10

  method M2(x: int := 3 / y, y: int := 10) // error: division by zero (despite precondition)
    requires y == 10

  method M3(x: int := 3, y: int := 10)
    requires y == 8
    requires 1 / x == 2000 // error: division by zero

  iterator Iter0(x: int := 8, y: int := 10 / x) // error: division by zero (reported twice)

  iterator Iter1(x: int, z: int := 10 / x) // error: division by zero (despite precondition) (reported twice)
    requires x == 10

  iterator Iter2(x: int := 3 / y, y: int := 10) // error: division by zero (despite precondition) (reported twice)
    requires y == 10

  iterator Iter3(x: int := 3, y: int := 10)
    requires y == 8
    requires 1 / x == 2000 // error: division by zero (reported twice)

  datatype Dt = Dt(x: int := 8, y: int := 10 / x) // error: division by zero (reported twice)

  function method Int(): int
  function method Nat(): int
    ensures 0 <= Nat()

  function SubrangeF0(x: nat := Int()): int // error: Int() may not be a "nat"
  method SubrangeM0(x: nat := Int()) // error: Int() may not be a "nat"
  iterator SubrangeI0(x: nat := Int()) // error: Int() may not be a "nat"
  datatype SubrangeD0 = D0(x: nat := Int()) // error: Int() may not be a "nat"

  function SubrangeF1(x: nat := Nat()): int
  method SubrangeM1(x: nat := Nat())
  iterator SubrangeI1(x: nat := Nat())
  datatype SubrangeD1 = D1(x: nat := Nat())

  iterator DependencyRegression(x: nat)
    // if the call graph dependencies are set up correctly, then
    requires assert 0 <= Nat(); 3 < 10  // there should be no complaints about this assertion
}

module Nested {
  function F(xt: int, yt: int := G(xt)): int // error: mutually recursive call not allowed in default-value expression
  function G(x: int, y: int := x): int {
    if x <= 0 then 0 else
      F(x - 1) // expands to F(x-1, G(x-1, x-1))
  }

  function F'(xt: int, yt: int := G'(xt)): int // error: mutually recursive call not allowed in default-value expression
    decreases 5
  {
    G'(xt) // there's a termination problem here, but the complaint is masked by the default value error 3 lines above
  }
  function G'(x: int, y: int := x): int
    decreases 6
  {
    F'(y) // expands to F'(y, G'(y, y)), but there's no additional complaint about the non-terminating call to G' (complaint was given above)
  }

  function K(xt: nat, yt: nat := if xt == 0 then 6 else L(xt - 1)): nat // error: mutually recursive call not allowed in default value
    decreases xt, 0
  function L(x: nat, y: nat := x): nat
    decreases x, 1
  {
    K(x) // should expand to: K(x, if x == 0 then 6 else L(x - 1))
  }

  function A(x: nat := B()): nat // error: mutually recursive call not allowed in default value
  function B(x: nat := C()): nat // error: mutually recursive call not allowed in default value
  function C(): nat
    decreases 7
  {
    ABC0() + ABC1() + ABC2()
  }
  function ABC0(): nat
    decreases 6
  {
    A(B(C())) // error: call to C may not terminate
  }
  function ABC1(): nat
    decreases 6
  {
    // the following expression expands to A(B(C()))
    A(B()) // error (x2): calls to A and B may not terminate
  }
  function ABC2(): nat
    decreases 6
  {
    // the following expression expands to A(B(C()))
    A() // error: call to A may not terminate
  }
}

module ReadsAndDecreases {
  // reads and decreases are not checked directly on default-valued expressions. Instead,
  // those are checked at call sites.
  class C {
    var data: int

    function M(x: int := data): int { x } // error: insufficient reads clause

    function NA(): int
      decreases 3
    {
      NCaller1(2, this)
    }
    function NB(x: int, y: int := NA()): int // error: mutually recursive call not allowed in default-value expression
      decreases x
    {
      NCaller0(x, this) + NCaller1(x, this)
    }

    // The following function has a division-by-zero error in the default-value expression
    // for "y". That's not allowed (even if all call sites pass in "x" as non-0), and it's
    // checked here.
    function O(x: int, y: int := 3 / x): int // error: division by zero
    {
      x + y
    }
  }

  function MCaller0(c: C): int {
    c.M() // no additional complaint
  }
  function MCaller1(c: C): int
    reads c
  {
    c.M()
  }
  function MCaller2(c: C): int {
    c.M(2)
  }

  function NCaller0(x: int, c: C): int
    decreases x, 0
  {
    if x <= 0 then 0 else c.NB(x - 1, 0)
  }
  function NCaller1(x: int, c: C): int
    decreases x, 0
  {
    // in the following line, c.NB(x - 1) expands to c.NB(x - 1, NA()), but the termination check for
    // NB has already been done in the default-value expression itself
    if x <= 0 then 0 else c.NB(x - 1)
  }

  function OCaller0(c: C): int {
    c.O(1) + c.O(0, 2)
  }
  function OCaller1(c: C): int {
    c.O(0) // no repeated warning about division-by-zero
  }
  function OCaller2(x: int, c: C): int
    requires x != 0
  {
    c.O(x)
  }

  function method J(): int
  lemma AboutJ()
    ensures J() != 0
  method Jx(x: int := AboutJ(); 2 / J()) // lemma ensures no div-by-zero
  method Jy() {
    Jx(); // no additional check here
  }

  lemma Lemma(x: int)
    requires x == 3
  function BadLemmaCall(y: int := Lemma(2); 5): int // error: precondition violation in lemma call
  method BadLemmaCaller() {
    var z := BadLemmaCall(); // no repeated complaint here
  }

  function MoreReads(a: array<int>, m: array2<int>,
    x: int := if 0 < a.Length then a[0] else 3, // error: insufficient reads clause
    y: int := if 0 < m.Length0 && 0 < m.Length1 then m[0, 0] else 3): int // error: insufficient reads clause
  function ReadA0(a: array<int>, m: array2<int>): int
    requires m.Length0 == 0
  {
    MoreReads(a, m)
  }
  function ReadA1(a: array<int>, m: array2<int>): int
    requires m.Length0 == 0
    reads a
  {
    MoreReads(a, m)
  }
  function ReadM0(a: array<int>, m: array2<int>): int
    requires a.Length == 0
  {
    MoreReads(a, m)
  }
  function ReadM1(a: array<int>, m: array2<int>): int
    requires a.Length == 0
    reads m
  {
    MoreReads(a, m)
  }
  function ReadNeither(a: array<int>, m: array2<int>): int
    requires a.Length == 0 == m.Length0
  {
    MoreReads(a, m)
  }
}

// Test well-formedness, subtypes, reads, and decreases

module WellformednessCheck {
  datatype R = R(i: int, x: int := 10 / i) // error: division by zero
  function F(i: int, x: int := 10 / i): int // error: division by zero
  method M(i: int, x: int := 10 / i) // error: division by zero
  iterator Iter(i: int, x: int := 10 / i) // error: division by zero (reported twice)
  class Class {
    constructor (i: int, x: int := 10 / i) // error: division by zero
  }

  method Caller(y: int) {
    // No additional errors are reported at the use sites
    if
    case true =>
      var z := R(y);
    case true =>
      var z := F(y);
    case true =>
      M(y);
    case true =>
      var z := new Iter(y);
    case true =>
      var z := new Class(y);
  }
}

module SubtypeCheck {
  datatype R = R(i: int, x: nat := i) // error: i is not a nat
  function F(i: int, x: nat := i): int // error: i is not a nat
  method M(i: int, x: nat := i) // error: i is not a nat
  iterator Iter(i: int, x: nat := i) // error: i is not a nat (reported twice)
  class Class {
    constructor (i: int, x: nat := i) // error: i is not a nat
  }

  method Caller(y: int) {
    // No additional errors are reported at the use sites
    if
    case true =>
      var z := R(y);
    case true =>
      var z := F(y);
    case true =>
      M(y);
    case true =>
      var z := new Iter(y);
    case true =>
      var z := new Class(y);
  }
}

module TerminationCheck {
  lemma X() {
    var r := R(5);
    var f := F(5) + G(5);
    M();
  }

  datatype R = R(x: int := X(); 3) // error: termination violation
  function F(x: int := F(5)): int // error: termination violation
  function G(x: int := X(); 3): int // error: termination violation
  lemma M(x: int := X(); 3) // error: termination violation

  method Caller() {
    // No additional errors are reported at the use sites
    if
    case true =>
      var z := R();
    case true =>
      var z := F();
    case true =>
      var z := G();
    case true =>
      M();
  }
}

module TerminationCheck_datatype {
  datatype Q = Q(x: int := Q(5).x)

  datatype R = R(x: int := F()) // error: mutual recursion not allowed in default values
  function method F(): int {
    R().x
  }

  datatype S = S(x: nat := X(); -3) // error: mutual recursion not allowed in default values
  lemma X()
    ensures false
  {
    X(); // error: termination violation
    var s := S();
  }
}

module TerminationCheck_tricky {
  datatype S = S(x: nat := False(); -3) // error: mutual recursion not allowed in default values
  lemma False()
    ensures false
  {
    var s := S();
    assert s.x == -3;
    assert 0 <= Id(s).x;
  }
  function method Id(s: S): S
    ensures 0 <= Id(s).x
  {
    var n: nat := s.x;
    s
  }
}

module TerminationCheck_tricky' {
  lemma False()
    ensures false
  {
    // Regression: With an explicit type ": R" for "r" in the following line, an error was
    // reported in this module. Good. But it was once the case that no error was reported
    // if the type ": R" was left implicit.
    var r := R();
    assert r.x == -3;
    Nat(r.x);
  }

  datatype R = R(x: nat := False(); -3) // error: mutual recursion not allowed in default values

  lemma Nat(n: nat)
    ensures 0 <= n
  {
  }
}

module TickRegressions {
  lemma X()
  // The uses of X() in the following declarations once caused malformed Boogie, because
  // the $Tick variable wasn't used in the necessary Boogie modifies clauess.
  const u: nat := (X(); -3) // error: -3 is not a nat
  datatype S = S(x: nat := X(); -3) // error: -3 is not a nat
}

module StmtExprCallPreconditionRegression {
  function G(): int
    // Amazingly, the well-formedness check for G was once omitted for this function.
    requires (X(); true) // error: precondition violation

  lemma X()
    requires false
  { }
}

module IteratorFrameRegression {
  lemma X()
  // The following once caused malformed Boogie, because the $_Frame variable had not been declared.
  iterator Iter()
    requires (X(); 3) == 3
  // The following once caused malformed Boogie, because the $_Frame variable had not been declared.
  iterator Iter'(x: int := X(); 3)
}

module ReadsCheck {
  class Cell {
    var data: int
  }
  datatype R = R(c: Cell, x: int := c.data) // error: reads violation
  function F(c: Cell, x: int := c.data): int // error: reads violation
  function G(c: Cell, x: int := c.data): int
    reads c
  function H(c: Cell, d: Cell, x: int := c.data): int // error: reads violation (check is done independent of preconditions)
    requires c == d
    reads d
  method M(c: Cell, x: int := c.data)
  iterator Iter(c: Cell, x: int := c.data)
  class Class {
    constructor (c: Cell, x: int := c.data)
  }

  method Caller(c: Cell) {
    // No additional errors are reported at the use sites
    if
    case true =>
      var z := R(c);
    case true =>
      var z := F(c);
    case true =>
      M(c);
    case true =>
      var z := new Iter(c);
    case true =>
      var z := new Class(c);
  }

  datatype D = D(c: Cell, x: int := c.data) // error: no reads allowed
}

module ExtremeOrdinal {
  greatest predicate P(x: int, u: int := x) {
    x == u
  }

  least predicate Q(x: int, u: int := x) {
    x == u
  }

  least lemma L(x: int, u: int := x)
    requires x == u
  {
  }

  lemma TestLeast(y: int, z: int, v: int, w: int, a: int, b: int, o: ORDINAL)
    requires !o.IsLimit
  {
    assert P(y);
    assert P#[o](z);
    L(v);
    L#[o](w);
    assert Q(a);
    assert Q#[o](b);
  }
}

module ExtremeNat {
  greatest predicate P[nat](x: int, u: int := x) {
    x == u
  }

  least predicate Q[nat](x: int, u: int := x) {
    x == u
  }

  least lemma L[nat](x: int, u: int := x)
    requires x == u
  {
  }

  lemma TestLeast(y: int, z: int, v: int, w: int, a: int, b: int, o: nat) {
    assert P(y);
    assert P#[o](z);
    L(v);
    L#[o](w);
    assert Q(a);
    assert o != 0 ==> Q#[o](b);
  }

  lemma TestLeastZero(y: int, z: int, v: int, w: int, a: int, b: int, o: nat) {
    assert Q#[o](b); // error: does not hold for o == 0
  }
}
