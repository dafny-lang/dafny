// RUN: %exits-with 4 %dafny /generalTraits:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ChildIsNonRefTrait {
  trait Parent {
    const yy: nat
    function F(umpa: int): nat
      requires yy < 300
      ensures F(umpa) < yy + 900

    method M() returns (p: nat)
      requires yy < 100
      ensures p < yy + F(5) + 900
  }

  trait Child extends Parent {
    function F(umpa: int): nat
      requires yy < 800
      ensures F(umpa) < yy + 100
    {
      2
    }

    method M() returns (p: nat)
      requires yy < 800
      ensures p < yy + F(5) + 100
    {
      p := yy + 101;
    }
  }

  trait ErrorChild extends Parent {
    function F(umpa: int): nat // error: postcondition violation
      requires yy < 800
      ensures F(umpa) < yy
    {
      2
    }

    method M() returns (p: nat)
      requires yy < 800
      ensures p < yy + F(5) + 100
    { // error: postcondition violation
      p := yy + 102;
    }
  }

  trait OverrideErrors extends Parent {
    function F(umpa: int): nat // error: precondition is stronger than in overridden function
      requires yy < 200
      ensures F(umpa) < yy + 100
    {
      2
    }

    method M() returns (p: nat) // error: postcondition is weaker than in overridden method
      requires yy < 150
      ensures p < yy + F(5) + 1200
    {
      p := yy + 101;
    }
  }

  method Test(tr: Parent, cl: Child)
    requires tr == cl as Parent
  {
    if cl.yy == 0 {
      var u := cl.F(19);
      var w := cl.M();
    }
  }
}

module ChildIsRefTrait {
  trait Trait {
    const yy: nat
    function F(umpa: int): nat
      requires yy < 300
      ensures F(umpa) < yy + 900

    method M() returns (p: nat)
      requires yy < 100
      ensures p < yy + F(5) + 900
  }

  trait ChildTrait extends Trait, object {
    function F(umpa: int): nat
      requires yy < 800
      ensures F(umpa) < yy + 100
    {
      2
    }

    method M() returns (p: nat)
      requires yy < 800
      ensures p < yy + F(5) + 100
    {
      p := yy + 101;
    }
  }

  trait ErrorChild extends Trait {
    function F(umpa: int): nat // error: postcondition violation
      requires yy < 800
      ensures F(umpa) < yy
    {
      2
    }

    method M() returns (p: nat)
      requires yy < 800
      ensures p < yy + F(5) + 100
    { // error: postcondition violation
      p := yy + 102;
    }
  }

  trait OverrideErrors extends Trait {
    function F(umpa: int): nat // error: precondition is stronger than in overridden function
      requires yy < 200
      ensures F(umpa) < yy + 100
    {
      2
    }

    method M() returns (p: nat) // error: postcondition is weaker than in overridden method
      requires yy < 150
      ensures p < yy + F(5) + 1200
    {
      p := yy + 101;
    }
  }

  method Test(tr: Trait, cl: ChildTrait)
    requires tr == cl as Trait
  {
    if cl.yy == 0 {
      var u := cl.F(19);
      var w := cl.M();
    }
  }
}

module ChildIsClass {
  trait Trait {
    const yy: nat
    function F(umpa: int): nat
      requires yy < 300
      ensures F(umpa) < yy + 900

    method M() returns (p: nat)
      requires yy < 100
      ensures p < yy + F(5) + 900
  }

  class Class extends Trait {
    function F(umpa: int): nat
      requires yy < 800
      ensures F(umpa) < yy + 100
    {
      2
    }

    method M() returns (p: nat)
      requires yy < 800
      ensures p < yy + F(5) + 100
    {
      p := yy + 101;
    }
  }

  trait ErrorChild extends Trait {
    function F(umpa: int): nat // error: postcondition violation
      requires yy < 800
      ensures F(umpa) < yy
    {
      2
    }

    method M() returns (p: nat)
      requires yy < 800
      ensures p < yy + F(5) + 100
    { // error: postcondition violation
      p := yy + 102;
    }
  }

  trait OverrideErrors extends Trait {
    function F(umpa: int): nat // error: precondition is stronger than in overridden function
      requires yy < 200
      ensures F(umpa) < yy + 100
    {
      2
    }

    method M() returns (p: nat) // error: postcondition is weaker than in overridden method
      requires yy < 150
      ensures p < yy + F(5) + 1200
    {
      p := yy + 101;
    }
  }

  method Test(tr: Trait, cl: Class)
    requires tr == cl as Trait
  {
    if cl.yy == 0 {
      var u := cl.F(19);
      var w := cl.M();
    }
  }
}
