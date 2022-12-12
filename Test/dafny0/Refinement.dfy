// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class X { }
  class T {
    method M(x: int) returns (y: int)
      requires 0 <= x;
      ensures 0 <= y;
    {
      y := 2 * x;
    }
    method Q() returns (q: int, r: int, s: int)
      ensures 0 <= q && 0 <= r && 0 <= s;
    {  // error: failure to establish postcondition about q
      r, s := 100, 200;
    }
  }
}

module B refines A {
  class C { }
  datatype Dt = Ax | Bx
  class T ... {
    method P() returns (p: int)
    {
      p := 18;
    }
    method M(x: int) returns (y: int)
      ensures y % 2 == 0;  // add a postcondition
    method Q ...
      ensures 12 <= r;
      ensures 1200 <= s;  // error: postcondition is not established by
                          // inherited method body
  }
}

// ------------------------------------------------

module A_AnonymousClass {
  class XX {
    var x: int;
    method Increment(d: int)
      modifies this;
    {
      x := x + d;
    }
  }
}

module B_AnonymousClass refines A_AnonymousClass {
  class XX ... {
    method Increment...
      ensures x <= old(x) + d;
  }
}

module C_AnonymousClass refines B_AnonymousClass {
  class XX ... {
    method Increment(d: int)
      ensures old(x) + d <= x;
    method Main()
      modifies this;
    {
      x := 25;
      Increment(30);
      assert x == 55;
      Increment(12);
      assert x == 66;  // error: it's 67
    }
  }
}

// ------------------------------------------------

module BodyFree {
  function F(x: int): int
    ensures 0 <= F(x);
  method TestF() {
    assert F(6) == F(7);  // error: no information about F so far
  }
  method M() returns (a: int, b: int)
    ensures a == b;
}

module SomeBody refines BodyFree {
  function F(x: int): int
  { if x < 0 then 2 else 3 }
  method TestFAgain() {
    assert F(6) == F(7);
  }
  method M() returns (a: int, b: int)
  {
    a := b;  // good
  }
}

module FullBodied refines BodyFree {
  function F(x: int): int
  { x } // error: does not meet the inherited postcondition
  method M() returns (a: int, b: int)
  {  // error: does not establish postcondition
    a := b + 1;
  }
}

// ------------------------------------------------

module Abstract {
  class MyNumber {
    ghost var N: int
    ghost var Repr: set<object>
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    constructor Init()
      ensures N == 0
      ensures Valid() && fresh(Repr)
    {
      N, Repr := 0, {this};
      new;
      assume Valid();
    }
    method Inc()
      requires Valid()
      modifies Repr
      ensures N == old(N) + 1
      ensures Valid() && fresh(Repr - old(Repr))
    {
      N := N + 1;
      assume Valid();
    }
    method Get() returns (n: int)
      requires Valid()
      ensures n == N
    {
      var k;  assume k == N;
      n := k;
    }
  }
}

module Concrete refines Abstract {
  class MyNumber ... {
    var a: int
    var b: int
    predicate Valid...
    {
      this in Repr &&
      N == a - b
    }
    constructor Init...
    {
      new;
      a := b;
      assert ...;
    }
    method Inc...
    {
      if * { a := a + 1; } else { b := b - 1; }
      ...;
      assert ...;
    }
    method Get...
    {
      var k := a - b;
      assert ...;
    }
  }
}

module Client {
  import C = Concrete
  class TheClient {
    method Main() {
      var n := new C.MyNumber.Init();
      n.Inc();
      n.Inc();
      var k := n.Get();
      assert k == 2;
    }
  }
}

module IncorrectConcrete refines Abstract {
  class MyNumber ... {
    var a: int
    var b: int
    predicate Valid...
    {
      this in Repr &&
      N == 2*a - b
    }
    constructor Init...
    {
      new;
      a := b;
      assert ...;  // error: Valid does not hold
    }
    method Inc...
    {
      if * { a := a + 1; } else { b := b - 1; }
      ...;
      assert ...;  // error: Valid does not hold
    }
    method Get...
    {
      var k := a - b;
      assert ...;  // error: assertion violation
    }
  }
}

// ------------------------------------------------

module Modify0 {
  class Cell {
    var data: int
  }

  method M(c: Cell)
    modifies c
    ensures c.data == 10
  {
    modify c;
    c.data := 10;
  }

  method N() returns (x: int)
    ensures x == 10
  {
    var i := 0;
    while i < 10
    x := 10;
  }

  method P() returns (x: int)
    ensures x == 10
  {
    x := 10;
  }

  method Q() returns (x: int)
    ensures x == 10
  {
    x := 10;
  }
}

module Modify1 refines Modify0 {
  method M... {
    modify ... {
      return; // error: a "return" here would cause a problem with the refinement
    }
    ...;
  }

  method N... {
    ...;
    while ... {
      return; // error: a "return" here would cause a problem with the refinement
      ...;
    }
    ...;
  }

  method P... {
    return; // error: a "return" here would cause a problem with the refinement
    ...;
  }

  method Q... {
    {
      return; // error: a "return" here would cause a problem with the refinement
    }
    ...;
  }
}
