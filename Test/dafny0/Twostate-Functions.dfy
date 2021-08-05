// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Basic {
  class U {
    var aa: int
    var bb: int
    var next: U?

    static twostate function H0(new u: U): int
      requires 10 <= old(u.aa)  // error: u is not available in the old state
    {
      5
    }

    static twostate function H1(new u: U): int
    {
      old(u.aa)  // error: u is not available in the old state
    }

    twostate function K0(u: U): int
    {
      u.aa  // error: reads clause must include u
    }

    twostate function K1(u: U): int
    {
      old(u.aa)  // note, no reads clause needed to read the old state
    }

    twostate predicate R(u: U)
      requires 10 <= old(u.aa)
      reads u
      ensures u.aa < old(u.aa) < 50 ==> R(u)
    {
      u.aa + old(u.aa) < 100
    }

    twostate function GG<T>(x: int, new t: T): real
      requires old(aa) <= aa && unchanged(`bb)
      reads this
      ensures old(aa) <= aa && bb == old(bb)
      decreases old(aa) - old(aa) + x
    {
      if 0 < x then
        GG(x-1, t)
      else
        x as real
    }

    twostate predicate AIsIncreased()
      reads this
    {
      old(aa) < aa
    }

    method AM(x: U, y: U)
      modifies y
      ensures unchanged(`aa) || AIsIncreased()
    {
      y.aa := y.aa + 1;
      assert y.AIsIncreased();
      assert x != y ==> !x.AIsIncreased();
      assert this != y ==> !AIsIncreased();
      if * {
        assert x.AIsIncreased();  // error: x and y may be equal
      } else {
        assert AIsIncreased();  // error: this and y may be equal
      }
    }

    method AThis()
      modifies this
      ensures AIsIncreased()
    {
      aa := aa + 3;
    }

    method AN()
      modifies this
    {
      aa := 10;
      AThis();
      assert 10 < aa;
      AM(this, this);
      assert 11 <= aa;
    }

    method HM()
    {
      var u := new U;
      ghost var x := K0(u);  // error: u is not new
    }

    twostate function Sw0(n: nat, x: U, new y: U): real
    {
      if n == 0 then 8.29 else Sw0(n-1, y, x)  // error: parameter 1 is not new enough
    }

    twostate function Sw1(n: nat, x: U, new y: U): real
      requires x == y
    {
      if n == 0 then 8.29 else Sw1(n-1, y, x)  // fine
    }
  }
}

module M0 {
  class C {
    var data: nat
  }
  twostate function F(x: int, c: C, new d: C): int
    reads c, d

  trait Tr {
    twostate function G(c: C?, new d: C): int
      requires c == null || unchanged(c)
      reads c, d
      ensures c != null ==> old(c.data) <= G(c, d)
    twostate lemma L(c: C, new d: C)
      requires unchanged(c)
      ensures old(c.data) <= G(c, d)
  }
  class Cl extends Tr {
    twostate function G(c: C?, new d: C): int
      requires c != null ==> c.data <= old(c.data)
      reads c
      ensures c != null ==> G(c, d) == c.data
      ensures 0 <= old(d.data)  // error: d is not available in old state
    {
      if c == null then 2 else c.data
    }
    twostate lemma L(c: C, new d: C)
      requires c.data <= old(c.data)
      ensures G(c, d) == c.data
    {
    }
  }
}

module M1 refines M0 {
  twostate function F...
  {
    x +
      old(c.data) +
      c.data +
      old(d.data) +  // error: d is not available in the old state
      d.data
  }
}

module Hof {
  class D {
    var data: int
    twostate function P(d: D): int
      reads d
    {
      d.data
    }
    method M(e: D) returns (ghost x: int)
    {
      var d := new D;
      if * {
        x := P(d);  // error: d was not available in the old state
      } else if * {
        ghost var p := P;
        x := p(d);  // error: precondition failure, since d was not available in the old state
      } else {
        ghost var p := P;
        x := p(e);  // fine
      }
    }
    // same thing as above, but with a static two-state function and method
    static twostate function Q(d: D): int
      reads d
    {
      d.data
    }
    static method N(e: D) returns (ghost x: int)
    {
      var d := new D;
      if * {
        x := Q(d);  // error: d was not available in the old state
      } else if * {
        ghost var q := Q;
        x := q(d);  // error: precondition failure, since d was not available in the old state
      } else {
        ghost var q := Q;
        x := q(e);  // fine
      }
    }
    method Lambda()
      requires data == 10
      modifies this
    {
      data := data + 8;
      ghost var f: () -> int := () => old(data);  // this is okay without a reads clause
      assert f() == 10;
    }
  }
}
