// RUN: %dafny /print:"%t.print" /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  class A {
    var f: int
    var g: A
  }

  twostate lemma L8(a: A, new b: A)
    requires a != null
    requires unchanged(a.g)
    modifies a.g  // lemmas are not allowed to have modifies clauses
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
      ensures unchanged(c)  // error: 'unchanged' not allowed here
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
      y.Floor  // error: incorrect result type
    }

    twostate function G(x: int, new u: object): real
      requires this != u
      requires old(aa) <= aa && unchanged(`bb)
      reads this
      reads old(next)  // error: not allowed to use 'old' in 'reads' clauses
      ensures old(aa) <= aa && old(G(x, u)) == G(x, u)
      decreases old(aa) - old(aa) + x
    {
      if 0 < x then
        G(x-1, u)
      else
        x as real
    }
  }
}
