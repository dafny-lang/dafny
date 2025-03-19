// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


trait Trait {
  // -----------------------
  method A0(x: nat)
  // default decreases: x
  method A1(x: nat)
  // default decreases: x
  method A2(x: nat)
    decreases x
  method A3(x: nat)
    decreases x
  // -----------------------
  method G0(x: nat, y: bool)
    decreases x, y
  method G1(x: nat, y: bool)
    decreases x+1, y
  method G2(x: nat, y: bool)
    decreases x
  method G3(x: nat, y: bool)
    decreases x+1, y
  method G4(x: nat, y: bool)
    decreases y, x
  method G5(x: nat, y: bool)
    decreases y, x
  method G6(x: nat, y: bool)
    decreases true, x
  method G7(x: nat, y: bool)
    decreases false, x
  method G8(x: nat, y: bool)
    requires x < 100
    decreases 120, y
  method G9(x: nat, y: bool)
    requires x < 100
    decreases 120, y
  method G10(x: nat, y: bool)
    requires x < 100
    decreases x, y
}

class Class extends Trait {
  // -----------------------
  method A0(x: nat)
  // default decreases: x
  { }
  method A1(x: nat)
    decreases x
  { }
  method A2(x: nat)
  // default decreases: x
  { }
  method A3(x: nat)
    decreases x
  { }
  // -----------------------
  method G0(x: nat, y: bool)
    decreases y, x  // error: opposite order from default
  { }
  method G1(x: nat, y: bool)
    decreases x, x  // fine -- it's below the one in the trait
  { }
  method G2(x: nat, y: bool)  // fine -- (x,y) is below the trait's (x,\top)
  // default decreases: x, y
  { }
  method G3(x: nat, y: bool)
    decreases x, y  // fine -- trait decrease is above this one
  { }
  method G4(x: nat, y: bool)
    decreases y, x+1  // error: this decreases is above the trait's decreases
  { }
  method G5(x: nat, y: bool)
    decreases y  // error: this is above the trait's decreases clause
  { }
  method G6(x: nat, y: bool)
    decreases y, x  // good -- this is the same or below the one in the trait
  { }
  method G7(x: nat, y: bool)
    decreases y, x  // error: this might be above the one in the trait
  { }
  method G8(x: nat, y: bool)
    decreases x, y  // fine -- given the precondition in the trait, this is below the one in the trait
  { }
  method G9(x: nat, y: bool)
    requires x < 105
    decreases 120, y  // fine -- given the precondition in the trait, this is below the one in the trait
  { }
  method G10(x: nat, y: bool)
    requires x < 100
    decreases 120, y  // error: this is above the one in the trait
  { }
}


trait TT {
  method M(x: int)
    decreases *
  method P(x: int)
    decreases *
}
class CC extends TT {
  method M(x: int)
    decreases x
  { }
  method P(x: int)
    decreases *
  { }
}


// The following module contains various regression tests
module More {
  trait A0 {
    ghost predicate P() decreases 5
  }
  class B0 extends A0 {
    ghost predicate P()  // error: rank is not lower
  }

  trait A1 {
    ghost predicate P() decreases 5
  }
  class B1 extends A1 {
    ghost predicate P() reads this  // error: rank is not lower
  }

  trait A2 {
    ghost predicate P(x: int)
  }
  class B2 extends A2 {
    ghost predicate P(x: int) reads this  // error: rank is not lower
  }

  trait A3 extends object {
    ghost predicate P() reads this
  }
  class B3 extends A3 {
    ghost predicate P()  // error: rank is not lower
  }

  trait A4 {
    ghost predicate P(x: int) decreases 5
  }
  class B4 extends A4 {
    ghost predicate P(x: int)  // error: rank is not lower
  }

  trait A5 {
    method M(x: int) decreases 5
  }
  class B5 extends A5 {
    method M(x: int)  // error: rank is not lower
  }
}
