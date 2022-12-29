// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export NotSoMuch
    reveals C, C.RevealedValid
    provides C.Valid, C.Get, C.M, C.x
  export More extends NotSoMuch
    reveals C.Get

  class C {
    var x: int;

    predicate Valid()
      reads this
      ensures Valid() ==> 0 <= x ensures x == 8 ==> Valid()  // holds for 8, does not hold for negative numbers

    predicate RevealedValid()
      reads this
      ensures Valid() ==> 0 <= x ensures x == 8 ==> Valid()  // holds for 8, does not hold for negative numbers

    function Get(): int
      reads this
    {
      x
    }

    constructor ()
      ensures Valid()
    {
      x := 8;
    }

    method M()
      requires Valid()
    {
      assert Get() == x;
      assert x == 8;  // error
    }
  }
}

module A' refines A {
  class C ... {
    // provide bodies for Valid, RevealedValid, and M
    predicate Valid...
    {
      x == 8
    }
    predicate RevealedValid...
    {
      x == 8
    }
    method N()
      requires Valid();
    {
      assert Get() == x;  // this is known, because the refined body of Get is considered inside A'
      assert x == 8;
    }
  }
}

abstract module B {
  import X : A`NotSoMuch
  method Main() {
    var c := new X.C();
    c.M();  // fine
    c.x := c.x + 1;
    c.M();  // error, because no body of Valid() is known
  }

  method L(c: X.C)
    modifies c;
  {
    assert c.Get() == c.x;  // error because Get() is only provided
    if * {
      assert c.Valid();  // error, because Valid() may be false (for example, if c.x is negative)
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is not known to hold for x==7
    } else {
      c.x := 8;
      assert c.Valid();  // fine, because the postcondition of Valid() says it holds for x==8
    }
  }
}

abstract module B_direct {
  import X : A'`NotSoMuch
  method Main() {
    var c := new X.C();
    if * {
      c.M();  // fine
      c.x := c.x + 1;  // this may ruin Valid()
      if * {
        assert c.Valid();  // error
      } else {
        c.M();  // error
      }
    } else {
      assert c.Valid();
      assert c.x == 8;  // error, because Valid is only provided
    }
  }

  method L(c: X.C)
    modifies c
  {
    assert c.Get() == c.x;  // error because Get() is only provided
    if * {
      assert c.Valid();  // error, because Valid() is only provided
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is only provided
    } else {
      c.x := 8;
      assert c.Valid();  // fine, because the postcondition of Valid() says it holds for x==8
    }
  }

  method K(c: X.C) {
    if * {
      assert c.Valid() ==> c.x == 8;  // error, because Valid() is only provided
    } else {
      assert c.RevealedValid() ==> c.x == 8;  // good
    }
  }
}

abstract module B_more {
  import X : A'`More
  method L(c: X.C)
    modifies c;
  {
    assert c.Get() == c.x;  // yes, this is known, due to using the larger export set of A'
  }
}

module B' refines B {
  import X = A'`NotSoMuch
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
    modifies c
  {
    assert c.Get() == c.x;  // error because Get() is only provided
    if * {
      assert c.Valid();  // error, because Valid() is only provided
    } else if * {
      c.x := 7;
      assert c.Valid();  // error, because Valid() is only provided
    } else if * {
      c.x := 8;
      assert c.Valid();  // fine, because Valid()'s postcondition says it holds for x==8
    } else {
      assert c.Valid() ==> c.x == 8;  // error, because Valid is only provided
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

function {:opaque} id<A>(x: A): A { x }

method id_ok()
{
  reveal id();
  assert id(1) == 1;
}

method id_fail()
{
  assert id(1) == 1;  // error
}

datatype Box<A> = Bx(A)

function {:opaque} id_box(x: Box): Box { x }

method box_ok()
{
  reveal id();
  assert id(Bx(1)) == Bx(1);
}

method box_fail()
{
  assert id(Bx(1)) == Bx(1);  // error
}

// ------------------------- opaque and layer quantifiers

module LayerQuantifiers
{
  function {:opaque} f(x: nat): bool { if x == 0 then true else f(x-1) }

  method rec_should_ok()
  {
    reveal f();
    assert f(1);
  }

  method rec_should_fail()
  {
    assert f(1);  // error
  }

  method rec_should_unroll_ok(one : int)
    requires one == 1
  {
    reveal f();
    // this one should have enough fuel
    assert f(one + one);
  }

  method rec_should_unroll_fail(one : int)
    requires one == 1
  {
    reveal f();
    assert f(one + one + one);  // error: this one does not have enough fuel
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
function {:opaque} zero<A>(): int { 0 }

// ------------------------- opaque for members of non-reference types

module TypeMembers {
  trait Tr {
    const fav: bool
    predicate method {:opaque} IsFavorite() {
      fav
    }
    static predicate method {:opaque} IsFive(x: int) {
      x == 5
    }
  }

  datatype Color = Carrot | Pumpkin
  {
    predicate method {:opaque} IsFavorite() {
      this == Pumpkin
    }
    static predicate method {:opaque} IsFive(x: int) {
      x == 5
    }
  }

  newtype Small = x | 30 <= x < 40 witness 30
  {
    predicate method {:opaque} IsFavorite() {
      this == 34
    }
    static predicate method {:opaque} IsFive(x: int) {
      x == 5
    }
  }

  method Test(tr: Tr, c: Color, s: Small) {
    if
    case tr.IsFavorite() =>
      assert tr.fav;  // error: this is not known here
    case c.IsFavorite() =>
      assert c == Pumpkin;  // error: this is not known here
    case s.IsFavorite() =>
      assert s == 34;  // error: this is not known here
    case tr.IsFavorite() =>
      reveal tr.IsFavorite();
      assert tr.fav;
    case c.IsFavorite() =>
      reveal c.IsFavorite();
      assert c == Pumpkin;
    case s.IsFavorite() =>
      reveal s.IsFavorite();
      assert s == 34;
    case true =>
      if tr.IsFavorite() && c.IsFavorite() && s.IsFavorite() {
        reveal tr.IsFavorite(), c.IsFavorite(), s.IsFavorite();
        assert !tr.fav || c == Carrot || s == 39;  // error: not true
      }
  }

  method StaticTest(x: int) {
    if
    case Tr.IsFive(x) =>
      assert x == 5;  // error: this is not known here
    case Color.IsFive(x) =>
      assert x == 5;  // error: this is not known here
    case Small.IsFive(x) =>
      assert x == 5;  // error: this is not known here
    case Tr.IsFive(x) =>
      reveal Tr.IsFive();
      assert x == 5;
    case Color.IsFive(x) =>
      reveal Color.IsFive();
      assert x == 5;
    case Small.IsFive(x) =>
      reveal Small.IsFive();
      assert x == 5;
    case true =>
      if Tr.IsFive(x) && Color.IsFive(x) && Small.IsFive(x) {
        reveal Tr.IsFive(), Color.IsFive(), Small.IsFive();
        assert x != 5;  // error: not true
      }
  }
}
