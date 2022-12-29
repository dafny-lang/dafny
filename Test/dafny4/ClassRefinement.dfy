// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

abstract module M0 {
  class Counter {
    ghost var N: int
    ghost var Repr: set<object>
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    constructor Init()
      ensures N == 0
      ensures Valid() && fresh(Repr)
    {
      Repr := {};
      new;
      ghost var repr :| {this} <= repr && fresh(repr - {this});
      N, Repr := 0, repr;
      assume Valid();  // to be verified in refinement module
    }

    method Inc()
      requires Valid()
      modifies Repr
      ensures N == old(N) + 1
      ensures Valid() && fresh(Repr - old(Repr))
    {
      N := N + 1;
      modify Repr - {this};
      assume Valid();  // to be verified in refinement module
    }

    method Get() returns (n: int)
      requires Valid()
      ensures n == N
    {
      n :| assume n == N;
    }
  }
}

module M1 refines M0 {
  class Cell {
    var data: int
    constructor (d: int)
      ensures data == d
    { data := d; }
  }

  class Counter ... {
    var c: Cell
    var d: Cell
    predicate Valid...
    {
      this in Repr &&
      c in Repr &&
      d in Repr &&
      c != d &&
      N == c.data - d.data
    }

    constructor Init...
    {
      c := new Cell(0);
      d := new Cell(0);
      new;
      ghost var repr := Repr + {this} + {c,d};
      ...;
      assert ...;
    }

    method Inc...
    {
      ...;
      modify ... {
        c.data := c.data + 1;
      }
      assert ...;
    }

    method Get...
    {
      n := c.data - d.data;
    }
  }
}

method Main() {
  var mx := new M1.Counter.Init();
  var my := new M1.Counter.Init();
  assert mx.N == 0 && my.N == 0;
  mx.Inc();
  my.Inc();
  mx.Inc();
  var nx := mx.Get();
  var ny := my.Get();
  assert nx == 2 && ny == 1;
  print nx, " ", ny, "\n";
}
