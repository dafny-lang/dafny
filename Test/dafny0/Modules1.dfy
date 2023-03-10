// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  import B = Babble
  class X {
    ghost function Fx(z: B.Z?): int
      requires z != null;
      decreases 5, 4, 3;
    { z.G() }  // fine; this goes to a different module
  }
  datatype Y = Cons(int, Y) | Empty
}

class C {
  method M() { }
  ghost function F(): int { 818 }
}

method MyMethod() { }



module Babble {
  class Z {
    method K() { }
    ghost function G(): int
      decreases 10, 8, 6;
    { 25 }
  }
}

ghost function MyFunction(): int { 5 }

class D { }

method Proc0(x: int)
  decreases x;
{
  if (0 <= x) {
    Proc1(x - 1);
  }
}

method Proc1(x: int)
  decreases x;
{
  if (0 <= x) {
    Proc0(x - 1);
  }
}

method Botch0(x: int)
  decreases x;
{
  Botch1(x - 1);  // error: failure to keep termination metric bounded
}

method Botch1(x: int)
  decreases x;
{
  Botch0(x);  // error: failure to decrease termination metric
}

// ------ modules ------------------------------------------------

module A_Visibility {
  export
    provides C, C.P

  class C {
    static ghost predicate P(x: int)
      ensures P(x) ==> -10 <= x;
    {
      0 <= x
    }
  }
  method Main() {
    var y;
    if (C.P(y)) {
      assert 0 <= y;  // this much is known of C.P
      assert 2 <= y;  // error
    } else {
      assert C.P(8);  // this is fine
    }
  }
}

module B_Visibility {
  import A = A_Visibility
  method Main() {
    var y;
    if (A.C.P(y)) {
      assert -10 <= y;  // this much is known of C.P
      assert 0 <= y;  // error
    } else {
      assert A.C.P(8);  // error: C.P cannot be established outside the declaring module
    }
  }
}

// ------ qualified type names ----------------------------------

module Q_Imp {
  class Node { constructor () { } }
  class Klassy {
    constructor Init()
  }
}

module Q_M {
  import Q = Q_Imp
  method MyMethod(root: Q.Node, S: set<Q.Node>)
    requires root in S;
  {
    var i := new Q.Node();
    var j := new Q.Node();
    assert i != j;  // fine
    var q := new Q.Klassy.Init();
  }
}

// ----- regression test -----------------------------------------

abstract module Regression {
  module A
  {
    ghost predicate p<c,d>(m: map<c,d>)

    lemma m<a,b>(m: map<a,b>)
      ensures exists m :: p(var m : map<a,b> := m; m)
  }

  abstract module B
  {
    import X : A
  }
}

// ----- const definitions in traits and modules, subject to export -----

module ModuleContainTraitAndClass {
  export X
    reveals g0
    reveals Trait, Class
    reveals Trait.s0, Trait.t0, Trait.t1
    reveals Class.r0, Class.c0, Class.c1
  export Y
    provides g0
    reveals Trait, Class
    provides Trait.s0, Trait.t0, Trait.t1
    provides Class.r0, Class.c0, Class.c1

  const g0 := 16
  const g1: int

  trait Trait {
    static const s0 := 17
    static const s1: int
    const t0 := 18
    const t1: int
  }

  class Class extends Trait {
    static const r0 := 19
    static const r1: int
    const c0 := 20
    const c1: int
  }

  method Tests0()
  {
    assert g0 == 16;
    assert Trait.s0 == 17;
    assert Class.r0 == 19;
  }

  method Tests1(t: Trait?, c: Class?)
    requires t != null && c != null
  {
    assert t.t0 == 18;
    assert c.t0 == 18;
    assert c.c0 == 20;
  }
}

module ModuleImportingTraitAndClassX {
  import M = ModuleContainTraitAndClass`X

  method Tests0()
  {
    assert M.g0 == 16;
    assert M.Trait.s0 == 17;
    assert M.Class.r0 == 19;
  }

  method Tests1(t: M.Trait?, c: M.Class?)
    requires t != null && c != null
  {
    assert t.t0 == 18;
    assert c.t0 == 18;
    assert c.c0 == 20;
  }
}

module ModuleImportingTraitAndClassY {
  import M = ModuleContainTraitAndClass`Y

  method Tests0()
  {
    assert M.g0 == 16;  // error: cannot determine this in Y
    assert M.Trait.s0 == 17;  // error: cannot determine this in Y
    assert M.Class.r0 == 19;  // error: cannot determine this in Y
  }

  method Tests1(t: M.Trait?, c: M.Class?)
    requires t != null && c != null
  {
    assert t.t0 == 18;  // error: cannot determine this in Y
    assert c.t0 == 18;  // error: cannot determine this in Y
    assert c.c0 == 20;  // error: cannot determine this in Y
  }
}
