// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class C {
    var x: int;
    protected predicate Valid()
      reads this;
    {
      0 <= x
    }
    protected function Get(): int
      reads this;
    {
      x
    }
    constructor ()
      ensures Valid();
    {
      x := 8;
    }
    
    method M()
      requires Valid();
    {
      assert Get() == x;
      assert x == 8;  // error
    }
  }
}
module A' refines A {
  class C {
    protected predicate Valid...
    {
      x == 8
    }
    method N()
      requires Valid();
    {
      assert Get() == x;
      assert x == 8;
    }
  }
}

module B {
  import X : A
  method Main() {
    var c := new X.C();
    c.M();  // fine
    c.x := c.x + 1;
    c.M();  // error, because Valid() is opaque
  }
  method L(c: X.C)
    modifies c;
  {
    assert c.Get() == c.x;  // error because Get() is opaque
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.x := 8;
      assert c.Valid();  // error, because Valid() is opaque
    }
  }
}
module B_direct {
  import X : A'
  method Main() {
    var c := new X.C();
    c.M();  // fine
    c.x := c.x + 1;
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.M();  // error, because Valid() is opaque
    }
  }
  method L(c: X.C)
    modifies c;
  {
    assert c.Get() == c.x;  // error because Get() s opaque
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.x := 8;
      assert c.Valid();  // error, because Valid() is opaque
    }
  }
}
module B' refines B {
  import X = A'  // this by itself produces no more error
  method Main'() {
    var c := new X.C();
    c.M();  // fine
    c.x := c.x + 1;
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.M();  // error, because Valid() is opaque
    }
  }
  method L'(c: X.C)
    modifies c;
  {
    assert c.Get() == c.x;  // error because Get() s opaque
    if * {
      assert c.Valid();  // error, because Valid() is opaque
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is opaque
    } else {
      c.x := 8;
      assert c.Valid();  // error, because Valid() is opaque
    }
  }
}

// ---------------------------------

module OpaqueFunctionsAreNotInlined {
  predicate {:opaque} F(n: int)
  {
    0 <= n < 100
  }

  method M()
  {
    var x := 18;
    assert F(x);  // error: cannot be determined, since F is opaque
  }

  method M'()
  {
    var x := 18;
    reveal F();
    assert F(x);
  }
}

// --------------------------------- opaque and refinement

module M0 {
  function {:opaque} F(): int
  { 12 }
}
module M1 refines M0 {
}

// ---------------------------------- opaque and generics

function{:opaque} id<A>(x : A):A { x }

method id_ok()
{
  reveal id();
  assert id(1) == 1;
}

method id_fail()
{
  assert id(1) == 1;
}

datatype Box<A> = Bx(A)

function{:opaque} id_box(x : Box):Box { x }

method box_ok()
{
  reveal id();
  assert id(Bx(1)) == Bx(1);
}

method box_fail()
{
  assert id(Bx(1)) == Bx(1);
}

// ------------------------- opaque and layer quantifiers

module LayerQuantifiers
{
  function{:opaque} f(x:nat) : bool { if x == 0 then true else f(x-1) }

  method rec_should_ok()
  {
    reveal f();
    assert f(1);
  }

  method rec_should_fail()
  {
    assert f(1);
  }

  method rec_should_unroll_ok(one : int)
    requires one == 1;
  {
    reveal f();
    // this one should have enough fuel
    assert f(one + one);
  }

  method rec_should_unroll_fail(one : int)
    requires one == 1;
  {
    reveal f();
    // this one does not have enough fuel
    assert f(one + one + one);
  }
}

// ------------------------------------- regression test

module Regression
{
  datatype List<A> = Nil | Cons(A, tl: List<A>)

  function Empty<A>(): List<A> { Nil }

  function {:opaque} Length<A>(s: List<A>): int
    ensures 0 <= Length(s)
  {
    if s.Cons? then 1 + Length(s.tl) else 0
  }

  lemma Empty_ToZero<A>()
    ensures Length<A>(Empty<A>()) == 0;  // this line once caused the verifier to crash
  {
    reveal Length();
  }
}

// This function used to cause a problem for the old version of opaque,
// but it's fine with the new fuel-based version
function{:opaque} zero<A>():int { 0 }

