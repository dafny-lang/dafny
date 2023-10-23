// RUN: %exits-with 2 %dafny /env:0 /print:"%t.print" /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  class A {
    var f: int
    var g: A
  }

  twostate lemma L8(a: A, new b: A)
    requires a != null
    requires unchanged(a.g)
    modifies a.g  // error: lemmas are not allowed to have modifies clauses
    decreases old(a.f)
  {}
}

module M1 {
  class C { var f: int }

  class K {
    var g: int

    method M(c: C)
      requires unchanged(c)  // error: 'unchanged' not allowed here
      ensures unchanged(c)
    lemma L(c: C)
      requires unchanged(c)  // error: 'unchanged' not allowed here
      ensures unchanged(c)  // allowed, just like 'old' is allowed, but useless here
    ghost function F(c: C): bool
      requires unchanged(c)  // error: 'unchanged' not allowed here
      ensures unchanged(c)  // error: 'unchanged' not allowed here
    twostate lemma L2(c: C, d: C)
      requires unchanged(c, d`f, `g, this`g)
      ensures unchanged(c)
    {
      assert g == this.g == (this).g == d.f;
    }
  }
}

module PrettyPrinting {
  twostate function F(x: int, new u: object): real
  {
    x as real
  }

  twostate predicate P(y: real, new u: object)
  {
    y.Floor as real == y
  }

  class U {
    twostate function G(x: int, new u: object): real
    {
      x as real
    }

    twostate predicate Q(y: real, new u: object)
    {
      y.Floor as real == y
    }

    static twostate function H(x: int, new u: object): real
    {
      x as real
    }

    static twostate predicate R(y: real, new u: object)
    {
      y.Floor as real == y
    }

    function MF(y: real, ghost g: int): char
    {
      'G'
    }

    twostate lemma LL(y: real, new u: object)
    {
    }
  }
}

module F {
  class U {
    var aa: int
    var bb: int
    var next: U

    static twostate function H(x: int, new u: object): real
    {
      assert u == this;  // error: 'this' is not in scope
      x as real
    }

    twostate predicate R(y: real, new u: object)
    {
      y.Floor  // error: incorrect result type (reported two lines above)
    }

    twostate function G(x: int, new u: object): real
      requires this != u
      requires old(aa) <= aa && unchanged(`bb)
      reads this
      reads old(next)  // error: not allowed to use 'old' in 'reads' clauses
      ensures old(aa) <= aa && old(G(x, u)) == G(x, u)  // error: cannot call G inside old
      decreases old(aa) - old(aa) + x
    {
      if 0 < x then
        G(x-1, u)
      else
        x as real
    }
  }
}

module G {
  class C { var f: int }
  twostate predicate P() { true }
  ghost function Fu(): int
    requires P()  // error: cannot use a two-state function here
    reads if P() then {null} else {}  // error: cannot use a two-state function here
    ensures P()  // error: cannot use a two-state function here
    decreases P()  // error: cannot use a two-state function here
    decreases old(c.f)  // error: cannot use 'old' here
  method Me(c: C) returns (b: bool)
    requires c != null
    requires P()  // error: cannot use a two-state function here
    modifies if P() then {null} else {}  // error: cannot use a two-state function here
    ensures P()
    decreases P()  // error: cannot use a two-state function here
    decreases old(c.f)  // error: cannot use 'old' here
  iterator Iter(c: C)
    requires c != null
    requires P()  // error: cannot use a two-state function here
    yield requires P()  // error: cannot use a two-state function here
    reads if P() then {null} else {}  // error: cannot use a two-state function here
    modifies if P() then {null} else {}  // error: cannot use a two-state function here
    ensures P()
    yield ensures P()
    decreases P()  // error: cannot use a two-state function here
    decreases old(c.f)  // error: cannot use 'old' here
  twostate function TF(c: C): int
    requires c != null
    requires P()
    reads if P() then {null} else {}  // error: cannot use a two-state function here
    ensures P()
    decreases P(), old(c.f), c.f
  twostate lemma TL(c: C)
    requires c != null
    requires P()
    ensures P()
    decreases P(), old(c.f), c.f
}

module H {
  class C { var f: int }
  twostate predicate P() { true }
  class YY {
    static twostate predicate Sp() { false }
  }
  ghost function Fu(): int
  {
    ghost var p: () -> bool := P;  // error: cannot use a two-state function in this context
    ghost var q: () -> bool := YY.Sp;  // error: cannot use a two-state function in this context
    if P() then 5 else 7  // error: cannot use a two-state function here
  }
  method Me(c: C) returns (b: bool)
    requires c != null
    ensures P()
  {
    assert P();
    ghost var p: () -> bool := P;
    ghost var q: () -> bool := YY.Sp;
  }
  class D {
    ghost function G(): int
    static method Sm(c: C) returns (ghost b: bool)
      requires c != null
      ensures P()
    {
      ghost var u := G();  // error: G requires receiver, which is not available here in static method
      ghost var g := G;  // error: G requires receiver, which is not available here in static method
      assert P();
      b := P();
      ghost var p: () -> bool := P;
      ghost var q: () -> bool := YY.Sp;
    }
  }
  iterator Iter(c: C)
    requires c != null
    ensures P()
    yield ensures P()
  {
  }
  twostate function TF(c: C): int
    requires c != null
    requires P()
    ensures P()
    decreases P(), old(c.f), c.f
  {
    if P() then 5 else
      var p: () -> bool := P;
      if p() then 7 else 9
  }
  twostate lemma TL(c: C)
    requires c != null
    requires P()
    ensures P()
    decreases P(), old(c.f), c.f
  {
    assert P();
    var p: () -> bool := P;
  }
  ghost function K(c: C): int
  {
    TL(c);  // error: cannot call two-state lemma from this context
    5
  }
}

module J {
  twostate predicate P() { true }
  method Me() returns (b: bool)
    ensures P()
  {
    assert P();
    b := P();  // error: cannot assign a ghost to a non-ghost
    var p': () -> bool; p' := P;  // error: cannot assign a ghost
  }
}

module OldWithinOld {
  class C {
    var data: int
    var next: C
    twostate function F(): int
    twostate lemma L()
    method M()
    {
      ghost var x0 := old(F());  // error: two-state function cannot be used inside 'old'
      ghost var x1 := old(L(); 5);  // error: two-state lemma cannot be used inside 'old'
      ghost var x2 := old(unchanged(this));  // error: unchanged cannot be used inside old
      ghost var x3 := unchanged(old(next));
      ghost var x4 := old(fresh(this));  // error: fresh cannot be used inside old
      ghost var x5 := fresh(old(next));
      ghost var x6 := old(old(data));  // error: old cannot be used inside old
    }
  }
}

module TraitsAndOldParameters {
  class C { }
  trait Tr {
    twostate predicate A(c: C)
    twostate predicate B(new c: C)
    twostate predicate P(c: C, new d: C)
    twostate lemma L(c: C)
    twostate lemma M(new c: C)
    twostate lemma N(c: C, new d: C)
  }
  class Cl extends Tr {
    twostate predicate A(new c: C)  // error: cannot change old to new
    twostate predicate B(c: C)  // error: cannot change new to old
    twostate predicate P(c: C, new d: C)
    twostate lemma L(new c: C)  // error: cannot change old to new
    twostate lemma M(c: C)  // error: cannot change new to old
    twostate lemma N(c: C, new d: C)
  }
}

// Print test for /dprint. Note, this same class is tested with /rprint in Test/dafny2/CalcDefaultMainOperator.dfy.
module PrintTest {
  function Five(): int { 5 }
  ghost function Six(): int { 6 }

  function Ten(): int {
    var f := Five();
    ghost var s := Six();
    assert s == 6;
    f + f
  }

  function TenAgain(): int {
    var ten :=
      var f := Five();
      ghost var s := Six();
      assert s == 6;
      f + f;
    ten
  }

  ghost function TenOnceMore(): int {
    var ten :=
      var f := Five();
      ghost var s := Six();
      assert s == 6;
      f + f;
    ten
  }

  ghost function Eleven(): int {
    var f, s := Five(), Six();
    f + s
  }

  ghost function Twelve(): int {
    var s, t := Six(), Six();
    s + t
  }

  function Twenty(): int {
    var x :| x == 10;
    x + x
  }

  function TwentyOne(): int {
    ghost var x :| x == 10 && Yes(x);
    assert x + x + 1 == 21;
    21
  }

  ghost predicate Yes(x: int) { true }

  type Odd = x |
    var rr := 2; x % rr == 1
    witness var ww := 2; ww + 7

  newtype NewOdd = x |
    var rr := 2; x % rr == 1
    witness var ww := 2; ww + 7

  type Even = x |
    var rr := 2; x % rr == 0
    ghost witness var ww := 2; ww + 8

  newtype NewEven = x |
    var rr := 2; x % rr == 0
    ghost witness var ww := 2; ww + 8
}

module TwoStateAt {
  class Cell {
    var data: int
    constructor (x: int)
      ensures data == x
    {
      data := x;
    }

    static twostate function Sum<Y>(c: Cell, y: Y): int
      reads c
    {
      c.Plus<Y>(y)
    }

    twostate function Plus<Y>(y: Y): int
      reads this
    {
      SP<Y>(this, y)
    }

    twostate lemma LL<Y>(y: Y)
      ensures old(data) < data
    {
      var g := data;
      IdentityLemma<Y>(this, y);
      Cell.IdentityLemma<int>(this, 0);
      this.IdentityLemma<Y>(this, y);
      assert data == g;
    }

    static twostate lemma IdentityLemma<Y>(c: Cell, y: Y) {
      assert old(c.data) == c.data;
    }

    function G(): int { 32 }
    lemma Theorem() { }
  }

  twostate function SP<Y>(c: Cell, y: Y): int
    reads c
  {
    old(c.data) + c.data
  }

  ghost function F(): int { 9 }

  method Test<Y>(c: Cell, b: bool, y: Y)
    requires c.data == 2
    modifies c
  {
    assert c.Plus(0) == 4;
    c.data := c.data + 3;
    label Five:
    assert Cell.Sum(c, y) == 7;
    assert Cell.Sum<int>@Five(c, 0) == 10;
    assert Cell.Sum@Five(c, 0) == 10;
    assert Cell.Sum<Y>@Five(c, y) == 10;
    assert Cell.Sum@Five(c, y) == 10;

    c.data := c.data + 1;
    assert SP<bv3>(c, 0) == 8;
    assert SP<Y>@DoesNotExist(c, y) == 11;  // error: label does not exist

    if b {
      label OnlyB:
      c.data := c.data + 10;
    } else {
      c.data := c.data + 20;
    }
    label PostIf:

    assert c.Plus<Y>@OnlyB(y) == 16 || c.Plus<int>@Five(0) == 26;  // error: usage is not dominated by OnlyB
    assert b ==> Cell.Sum@PostIf(c, y) == 32;

    ghost var z := F@Five();  // error: F is not a two-state function
  }

  twostate lemma TwoLemma<Y>(c: Cell, y: Y)
    requires 2 * old(c.data) <= Cell.Sum<Y>(c, y)
    ensures old(c.data) <= SP<int>(c, 0) == SP<Y>(c, y) == c.Plus(0)
  {
  }

  method CallLemmas<Y>(c: Cell, b: bool, y: Y)
    modifies c
  {
    c.data := c.data + 1;
    label OneMore:
    if -1 <= old(c.data) {
      TwoLemma<Y>(c, y);
    }

    c.data := c.data + 4;
    label FiveMore:
    TwoLemma<int>@OneMore(c, 0);

    if b {
      c.data := c.data - 10;
      TwoLemma<Y>@FiveMore(c, y);
    } else {
      c.data := c.data + 2;
      TwoLemma<int>@After(c, 0);  // error: After is not in scope
    }
    c.LL(y);
    c.LL<Y>(y);
    c.LL<bv3>(0);
    label After:

    var g := c.G@FiveMore();  // error: G is not a two-state lemma
    c.Theorem@OneMore();  // error: Theorem is not a two-state lemma
  }

  method ExprAt(c: Cell, f: int -> int, g: int -> int, b: bool) {
    label L:
    var plus := c.Plus<int>;
    var xL := plus@L(0);  // error: cannot apply @L to an expression LHS
    // Note, the following two lines are rejected by the parser
    // var plusL := c.Plus<int>@L; // error (this could be allowed, but isn't supported yet)
    // var e := (if b then f else g)@L(0); // error (this never makes sense)
  }

  twostate lemma ReturnSomething(c: Cell) returns (x: int, d: Cell) {
    d := c;
  }

  method CallTwo(c: Cell)
    modifies c
  {
    c.data := 16;
    label L:
    var x, d := ReturnSomething@L(c);
  }

  ghost function {:opaque} OrdinaryOpaque(): int { 12 }
  method UseOrdinaryOpaque() {
    label L:
    reveal OrdinaryOpaque();
    reveal OrdinaryOpaque;  // error: missing parentheses
    reveal OrdinaryOpaque@K();  // error: label K not in scope
    reveal OrdinaryOpaque@L();  // error: @ can only be applied to something two-state (error message can be improved)
  }
  ghost function FuncUseOrdinaryOpaque(): int {
    reveal OrdinaryOpaque();
    reveal OrdinaryOpaque;  // error: missing parentheses
    reveal OrdinaryOpaque@K();  // error: label K not in scope
    10
  }
  twostate function {:opaque} Opaque(): int { 12 }
  method UseOpaque() {
    label L:
    reveal Opaque();
    reveal Opaque;  // error: missing parentheses
    reveal Opaque@K();  // error: label K not in scope
    reveal Opaque@L();  // error: all parameters in a reveal must be implicit, including labels
  }
  ghost function FuncUseOpaque(): int {
    reveal Opaque();  // error: cannot call two-state lemma in one-state function
    reveal Opaque;  // error: missing parentheses
    reveal Opaque@K();  // error: label K not in scope
    10
  }
  twostate function TwoFuncUseOpaque(): int {
    reveal Opaque();
    reveal Opaque;  // error: missing parentheses
    reveal Opaque@K();  // error: label K not in scope
    10
  }

  twostate lemma EasyTwo()
    ensures true
  ghost function CallEasy(): int {
    EasyTwo();  // error: two-state lemma cannot be called from one-state function
    9
  }
}

module OlderParameters {
  class C { }
  trait Tr {
    ghost predicate P(a: C)
    ghost predicate Q(older a: C)
    twostate predicate X(a: C)
    twostate predicate Y(new a: C)
  }
  class Good extends Tr {
    ghost predicate P(a: C)
    ghost predicate Q(older a: C)
    twostate predicate X(a: C)
    twostate predicate Y(new a: C)
  }
  class Bad extends Tr {
    ghost predicate P(older a: C) // error: cannot change non-older to older
    ghost predicate Q(a: C) // error: cannot change older to non-older
    twostate predicate X(new a: C) // error: cannot change from non-new to new
    twostate predicate Y(a: C) // error: cannot change from new to non-new
  }
}

module RefinementBase {
  class C { }
  ghost predicate P(a: C)
  ghost predicate Q(older a: C)
  twostate predicate X(a: C)
  twostate predicate Y(new a: C)
}

module GoodRefinement refines RefinementBase {
  ghost predicate P(a: C) { true }
  ghost predicate Q(older a: C) { true }
  twostate predicate X(a: C) { true }
  twostate predicate Y(new a: C) { true }
}

module BadRefinement refines RefinementBase {
  ghost predicate P(older a: C) { true } // error: cannot change non-older to older
  ghost predicate Q(a: C) { true } // error: cannot change older to non-older
  twostate predicate X(new a: C) { true } // error: cannot change non-new to new
  twostate predicate Y(a: C) { true } // error: cannot change new to non-new
}

module RevealInsideIterator {
  ghost function {:opaque} G(): int { 2 }

  iterator Iter(x: int) yields (r: int)
  {
    reveal G();
  }
}
