// RUN: %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AssignmentToNat {
  method M(x0: int, x1: int, x2: int, x3: int)
  {
    var a: nat := x0;  // error
    a := x1;  // error
    var z;
    z := var b: nat := x2; b;  // error
    z := var b: nat :| b == x3; b;  // error
  }
  method M'(x0: int, x1: int, x2: int, x3: int, x4: int)
  {
    var c: nat :| c == x0;  // error
    c :| c == x1;  // error

    var g := new G;
    g.u := x2;  // error

    var y := F(x3);  // error

    M''(x4);  // error
  }
  method M''(x: nat)

  function method F(q: nat): int
  function method F'(x: int): nat
  {
    F      // error (regarding result of F(x))
      (x)  // error (regaring argument to F)
  }

  class G {
    var u: nat
  }

  function method Pf(n: nat): int
  function method Pg(x: int): nat

  method P(x: int, f: nat -> int) returns (g: int -> nat)
    requires f.requires(x)  // error
  {
    var y := f(x);  // error
  }
  method Q(x: int) {
    var f := Pf;
    var g := Pg;
    var a := f(x);  // error
  }

  function Id(x: int): nat
  {
    x  // error
  }
}

module AssignmentToSetNat {
  method M(x0: set<int>, x1: set<int>, x2: set<int>, x3: set<int>)
  {
    var z;
    z := var b: set<nat> :| b == x3; b;  // error
  }
  method M'(x0: set<int>, x1: set<int>, x2: set<int>, x3: set<int>, x4: set<int>)
  {
    var c: set<nat> :| c == x0;  // error
    c :| c == x1;  // error
    var g := new G;
  }
  method M''(x: set<nat>)

  class G {
    var u: set<nat>
  }

  function method Pf(n: set<nat>): set<int>
  function method Pg(x: set<int>): set<nat>

  method Q(x: set<int>) {
    var f := Pf;
    var g := Pg;
  }
}

module OutParameters {
  method P<T>(x: T) returns (y: T) { y := x; }

  method M() returns (x: int, n: nat) {
    if {
      case true =>  x := P<nat>(n);
      case true =>  n := P<nat>(x);  // error (x)
      case true =>  x := P<int>(n);
      case true =>  n := P<int>(x);  // error (n)
    }
  }
}
