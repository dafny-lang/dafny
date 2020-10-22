// RUN: %dafny /env:0 /print:"%t.print" /dprint:- "%s" > "%t"
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
    function F(c: C): bool
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

    function method MF(y: real, ghost g: int): char
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
  function Fu(): int
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
  function Fu(): int
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
    function G(): int
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
  function K(c: C): int
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
