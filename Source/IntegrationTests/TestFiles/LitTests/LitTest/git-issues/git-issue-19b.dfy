// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


// Verification (for resolution, see git-issue-19a.dfy)

module M0 {
  class Basic {
    var data: int
  }

  class Cell {
    const x: int
    var y: int
    constructor (x: int, y: int)
      decreases if x == y == 0 then 0 else 1
    {
      this.x, this.y := x, y;
      if !(x == y == 0) {
        var anotherCell := new Cell(0, 0);
      }
    }
  }

  method P0()
    requires forall c: Basic :: c.data == 8
  {
    var o := new Basic;
    o.data := 8;
    assert forall c: Basic :: c.data == 8;  // fine
  }

  method P1()
    requires forall c: Basic :: c.data == 8
  {
    var o := new Basic;
    assert forall c: Basic :: c.data == 8; // error: might not hold for the new o
  }

  method Q()
    requires forall c: Basic :: c.data == 8
  {
    var o := new object;
    assert forall c: Basic :: c.data == 8; // error: the new object may be a Basic for all we know
  }

  method M0()
    requires forall c: Cell :: c.x == 8
  {
    var o := new Cell(7, 8);
    assert forall c: Cell :: c.x == 8; // error: does not hold for o (or for anotherCell)
  }

  method M1()
    requires forall c: Cell :: c.x == 8
  {
    var o := new Cell(8, 8);
    assert forall c: Cell :: c.x == 8; // error: does not hold for anotherCell
  }

  method N0()
    requires forall c: Cell :: c.y == 8
  {
    var o := new Cell(8, 7);
    assert forall c: Cell :: c.y == 8; // error: does not hold for o (or for anotherCell)
  }

  method N1()
    requires forall c: Cell :: c.y == 8
  {
    var o := new Cell(8, 8);
    assert forall c: Cell :: c.y == 8; // error: does not hold for anotherCell
  }
}

module M1 {
  class Basic {
    var data: int
  }

  method P1'()
    requires forall c: Basic :: c.data == 8
  {
    var o := new Basic;
    assert forall c: Basic :: c != o ==> c.data == 8; // fine
  }
}

module M2 {
  class Cell {
    const x: int
    constructor (x: int)
      ensures this.x == x
    {
      this.x := x;
    }
  }

  method M0()
    requires forall c: Cell :: c.x == 8
  {
    var o := new Cell(7);
    assert false; // error
  }
}

module M3 {
  class Cell {
    const x: int

    constructor Init0(x: int)
      requires forall c: Cell :: c.x == 8
      ensures this.x == x
      ensures forall c: Cell :: c.x == 8 // error: cannot prove this, unless we require x == 8 !
      decreases if x == 0 then 0 else 1
    {
      this.x := x;
      if !(x == 0) {
        var anotherCell := new Cell.Init0(0);
      }
    }

    constructor Init1(x: int, b: bool := true)
      requires forall c: Cell :: c.x == 8
      requires x == 8 // here, we require that x is 8
      ensures this.x == x
      ensures forall c: Cell :: c.x == 8
      decreases b
    {
      this.x := x;
      if !(x == 0) && b {
        var anotherCell := new Cell.Init1(0, false); // error: precondition violation
      }
    }

    constructor Init2(x: int, b: bool := true)
      requires forall c: Cell :: c.x == 8
      requires x == 8 // here, we require that x is 8
      ensures this.x == x
      ensures forall c: Cell :: c.x == 8 // this is actually ensured by this constructor, and the verifier knows it!
      decreases b
    {
      this.x := x;
      if !(x == 0) && b {
        var anotherCell := new Cell.Init2(8, false); // and here we pass in 8
      }
    }
  }

  method M()
    requires forall c: Cell :: c.x == 8
  {
    var o;
    if {
      case true => o := new Cell.Init0(8);
      case true => o := new Cell.Init1(8);
      case true => o := new Cell.Init2(8);
    }
    assert forall c: Cell :: c.x == 8;
  }
}

module M200 {
  ghost predicate P<T>(x: T)

  ghost predicate AllP<T>()
    reads **
  { forall x :: P<T>(x) }

  class C {}

  method M1()

  method M2()
  {
    assume forall x: C :: P<C>(x);
    M1();
    assert forall x: C :: P<C>(x); // error: the previous line may change the allocation state, so this assertion may no longer hold
  }

  method M3()
  {
    assume forall x: C :: P<C>(x);
    M1();
    assert AllP<C>(); // error: the previous line may change the allocation state, so AllP() may no longer hold
    assert forall x: C :: P<C>(x);
  }

  // a more concrete test

  class Cell { var data: int }

  ghost predicate Always100()
    reads **
  {
    forall c: Cell :: c.data == 100
  }

  lemma Lemma() {
  }

  method AMethodIsAMethod() {
    var c := new Cell;
    c.data := 101;
  }

  method TestStarStar()
    requires Always100()
  {
    Lemma();
    assert Always100(); // yes, nothing in the state has changed so far
    AMethodIsAMethod();
    assert Always100(); // error: the previous line may change the allocation state, so Always100() may no longer hold
  }
}
