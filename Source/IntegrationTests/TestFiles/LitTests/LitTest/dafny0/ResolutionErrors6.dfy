// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// ----- bad use of types without auto-initializers -----

module Initialization {
  datatype Yt<Y> = MakeYt(x: int, y: Y)
  type Even = x | x % 2 == 0
  type Odd = x | x % 2 == 1 witness 17
  type GW = x | x % 2 == 1 ghost witness 17

  method DefiniteAssignmentViolation() returns (e: Yt<Even>, o: Yt<Odd>, g: Yt<GW>)
  {
  }  // no resolution errors (but verification errors, see NonZeroInitialization.dfy)

  method ArrayElementInitViolation() returns (e: array<Yt<Even>>, o: array<Yt<Odd>>, g: array<Yt<GW>>)
  {
    e := new Yt<Even>[20];
    o := new Yt<Odd>[20];
    g := new Yt<GW>[20];
  }  // no resolution errors (but verification errors, see NonZeroInitialization.dfy)

  method GimmieOne<G(0)>() returns (g: G)
  {
  }

  method TypeParamViolation() returns (e: Yt<Even>, o: Yt<Odd>, g: Yt<GW>)
  {
    e := GimmieOne<Yt<Even>>();
    o := GimmieOne<Yt<Odd>>();
    g := GimmieOne<Yt<GW>>();  // error: cannot pass Yt<GW> to a (0)-parameter
  }
}

// ----------------- regression tests ----------------------------------------------------

module FreshTypeInferenceRegression {
  class MyClass {
    method M(N: nat)
    {
      var i, os := 0, {};
      while i < N
        invariant fresh(os)
        invariant forall o :: o in os ==> fresh(o.inner)  // error: type of "o" not yet known (this once caused a crash)
      {
        var o := new Outer();
        os, i := os + {o}, i + 1;
      }
    }
  }

  class Outer {
    const inner: Inner

    constructor ()
      ensures fresh(inner)
    {
      inner := new Inner();
    }
  }

  class Inner {
    constructor ()
  }
}

module RegressionTest {
  class Cache<X> {
    method Lookup(K: X) returns (V: X)
    {
      V := Cache[K];  // error: Cache is not a field but a type
    }
  }
}

module ExistsImpliesWarning {
  method M(a: array<int>, b: array<int>)
    requires a.Length == b.Length
    requires exists i :: 0 <= i < a.Length ==> a[i] == b[i]  // warning
    requires exists i :: true && (0 <= i < a.Length ==> a[i] == b[i])
    requires exists i :: (0 <= i < a.Length ==> a[i] == b[i])
    requires exists i | 0 <= i < a.Length :: true ==> a[i] == b[i]
    requires exists i | 0 <= i < a.Length :: a[i] == b[i]
    requires exists i | 0 <= i < a.Length ==> a[i] == b[i] :: true
    requires exists i :: !(0 <= i < a.Length) || a[i] == b[i]
    requires exists i :: a[i] == b[i] <== 0 <= i < a.Length  // warning
    requires exists i :: !(0 <= i < a.Length && a[i] != b[i])
    requires exists i :: 0 <= i < a.Length && a[i] == b[i]
    requires exists i :: true ==> (0 <= i < a.Length && a[i] == b[i])  // warning
  {
  }

  method N(a: array<int>, b: array<int>)
    requires a.Length == b.Length
    requires forall i :: 0 <= i < a.Length ==> a[i] == b[i]
    requires forall i :: true && (0 <= i < a.Length ==> a[i] == b[i])
    requires forall i :: (0 <= i < a.Length ==> a[i] == b[i])
    requires forall i | 0 <= i < a.Length :: true ==> a[i] == b[i]
    requires forall i | 0 <= i < a.Length :: a[i] == b[i]
    requires forall i | 0 <= i < a.Length ==> a[i] == b[i] :: true
    requires forall i :: !(0 <= i < a.Length) || a[i] == b[i]
    requires forall i :: a[i] == b[i] <== 0 <= i < a.Length
    requires forall i :: !(0 <= i < a.Length && a[i] != b[i])
    requires forall i :: 0 <= i < a.Length && a[i] == b[i]
    requires forall i :: true ==> (0 <= i < a.Length && a[i] == b[i])
  {
  }
}

// --------------- ghost (regression) tests, receivers -------------------------------------

module GhostReceiverTests {
  class C {
    ghost function F(x: int): int { 3 }
    function G(x: int): int { 4 }
    lemma L(x: int) { }
    method M(x: int) { }
  }

  method Caller(x: int, ghost z: int, c: C, ghost g: C) {
    {
      var y;
      y := c.F(x);  // error: LHS is non-ghost, so RHS cannot use ghost function F
      y := g.F(x);  // error: LHS is non-ghost, so RHS cannot use ghost function F
      y := c.G(x);
      y := g.G(x);  // error: LHS is non-ghost, so RHS cannot use ghost variable g
    }
    {
      // all of the these are fine, because: the LHS is ghost and, therefore, the whole statement is
      ghost var y;
      y := c.F(x);
      y := g.F(x);
      y := c.G(x);
      y := g.G(x);
    }
    {
      // all of the these are fine, because: the LHS is ghost and, therefore, the whole statement is
      ghost var y;
      y := c.F(z);
      y := g.F(z);
      y := c.G(z);
      y := g.G(z);
    }
    c.L(x);
    g.L(x);
    c.M(x);
    g.M(x);  // error: cannot pass ghost receiver to compiled method
  }
}

// --------------- ghost RHS of constants (regression) tests -------------------------------------

module GhostRhsConst {
  class C {
    ghost function F(n: nat): nat { n }  // a ghost function
    static ghost function G(n: nat): nat { n }  // a ghost function
    const b := F(0)  // error: RHS uses a ghost function
    static const u := G(0)  // error: RHS uses a ghost function
  }

  trait R {
    ghost function F(n: nat): nat { n }  // a ghost function
    static ghost function G(n: nat): nat { n }  // a ghost function
    const b := F(0)  // error: RHS uses a ghost function
    static const u := G(0)  // error: RHS uses a ghost function
  }
}

// --------------- errors from nested modules -------------------------------------

module ErrorsFromNestedModules {
  method M() {
    U.V.Test();
    UU.V.Test();
  }

  module U {  // regression test: since U is rather empty, this had once caused an error
    module V {
      method Test() {
      }
      module W {
        const x1 := 12 * false  // error: bad types
      }
    }
  }

  module UU.V {  // same regression as above
    method Test() {
    }
    module W {
      const x1 := 12 * false  // error: bad types
    }
  }
}

// --------------- name clashes related to prefix-named modules -------------------------------------

module NameClashes {
  module U.G {
  }
  module U {
    class G { }  // error: duplicate name: G
    class H { }
  }
  module U.H {  // error: duplicate name: H
  }
}

// --------------- regression ghost tests -------------------------------------

module RegressionGhostTests {
  class Cell {
    var data: int
  }

  method field(x: Cell)
    modifies x
  {
    ghost var y := x;
    x.data := 42;
    y.data := 42;  // error: assignment to non-ghost field depends on a ghost
    (assert x == y; x).data := 42;
    (assert x == y; y).data := 42;  // error: assignment to non-ghost field depends on a ghost
  }

  method arr(a: array<int>)
    requires 5 < a.Length
    modifies a
  {
    ghost var b := a;
    ghost var i := 5;
    a[i] := 42;  // error: assignment to non-ghost field depends on a ghost
    b[5] := 42;  // error: assignment to non-ghost field depends on a ghost
  }

  method arr2(a: array2<int>)
    requires 5 < a.Length0 && 5 < a.Length1
    modifies a
  {
    ghost var b := a;
    ghost var i := 5;
    a[i,5] := 42;  // error: assignment to non-ghost field depends on a ghost
    a[5,i] := 42;  // error: assignment to non-ghost field depends on a ghost
    b[5,5] := 42;  // error: assignment to non-ghost field depends on a ghost
  }
}

// --------------- regression test const in frame expression ------------------------------

module RegressionConstFrameExpression {
  class C {
    const x: int
    var y: int
  }
  method m(c: C)
    modifies c`x
    modifies c`y
    ensures unchanged(c`x)
    ensures unchanged(c)
  {

  }
}

// --------------- change in language semantics to forbid !! on maps ------------------------------

module MapDisjointnessNoMore {
  method M<X,Y>(a: map, b: map) {
    assert a !! b;  // error: !! is (no longer) support on maps
    assert a.Keys !! b.Keys;  // instead, this is the way to do it
  }
}

// --------------- expect statements ------------------------------

module ExpectStatements {
  ghost function UnsafeDivide(a: int, b: int): int {
    expect b != 0;  // expect statement is not allowed in this context
    a / b
  }

  method M() {
    ghost var g := 5;
    expect forall i : int :: i == i;  // error: quantifiers in non-ghost contexts must be compilable
    expect false, if g == 5 then "boom" else "splat"; // error: ghost variables are allowed only in specification contexts
  }
}

// --------------- type-parameter scopes ------------------------------

module TypeParameterScopes {
  class C<X> {
    function G(): X

    method M<X>(f: X) {
      var h: X := f;
      var k: X := G();  // error: this is the wrong X
    }

    function F<X>(f: X): int {
      var h: X := f;
      var k: X := G();  // error: this is the wrong X
      10
    }
  }
}

// --------------- type of function members (regression tests) ------------------------------

module TypeOfFunctionMember {
  ghost function Fo<X>(x: X): int

  lemma M() {
    // Both of the following once crashed the type checker
    var rd := Fo<real>.reads;
    var rq := Fo<real>.requires;
  }
}

// --------------- update operations ------------------------------

module CollectionUpdates {
  // Update operations on collections must have the right types, modulo subset types.
  // For verification errors, see Maps.dfy.
  trait Trait { }
  class Elem extends Trait { }

  method UpdateValiditySeq(d: Trait, e: Elem) {
    var s: seq<Elem> := [e, e, e, e, e];
    s := s[1 := d];  // error: d is not an Elem (and is not a subset type of it, either)
  }

  method UpdateValidityMultiset(d: Trait) {
    var s: multiset<Elem>;
    s := s[d := 5];  // error: element value is not a Elem
  }

  method UpdateValidityMap(d: Trait, e: Elem) {
    var m: map<Elem, Elem>;
    if * {
      m := m[d := e];  // error: key is not a Elem
    } else {
      m := m[e := d];  // error: value is not a Elem
    }
  }
}

// --------------- update operations ------------------------------

module MoreAutoInitAndNonempty {
  type A(0)
  type B(00)
  type C

  method Q<F(0)>(f: F)
  method P<G(00)>(g: G)
  method R<H>(h: H)

  function FQ<F(0)>(f: F): int
  function FP<G(00)>(g: G): int
  function FR<H>(h: H): int

  method M<X(0), Y(00), Z>(x: X, y: Y, z: Z)
  {
    Q(x);
    P(x);
    R(x);
    Q(y);  // error: auto-init mismatch
    P(y);
    R(y);
    Q(z);  // error: auto-init mismatch
    P(z);  // error: auto-init mismatch
    R(z);
  }

  method N<X(0), Y(00), Z>(x: X, y: Y, z: Z) returns (u: int)
  {
    u := FQ(x);
    u := FP(x);
    u := FR(x);
    u := FQ(y);  // error: auto-init mismatch
    u := FP(y);
    u := FR(y);
    u := FQ(z);  // error: auto-init mismatch
    u := FP(z);  // error: auto-init mismatch
    u := FR(z);
  }
}
