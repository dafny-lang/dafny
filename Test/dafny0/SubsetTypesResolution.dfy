// RUN: %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AssignmentToNat {
  method M(x0: int, x1: int, x2: int, x3: int)
  {
    var a: nat := x0;
    a := x1;
    var z;
    z := var b: nat := x2; b;
    z := var b: nat :| b == x3; b;
  }
  method M'(x0: int, x1: int, x2: int, x3: int, x4: int)
  {
    var c: nat :| c == x0;
    c :| c == x1;

    var g := new G;
    g.u := x2;

    var y := F(x3);

    M''(x4);
  }
  method M''(x: nat)

  function method F(q: nat): int
  function method F'(x: int): nat
  {
    F
      (x)
  }

  class G {
    var u: nat
  }

  function method Pf(n: nat): int
  function method Pg(x: int): nat

  method P(x: int, f: nat -> int) returns (g: int -> nat)
    requires f.requires(x)
  {
    var y := f(x);
    g := z => z;  // error: cannot find a type for RHS that is assignable to LHS
  }
  method Q(x: int) {
    var f := Pf;
    var g := Pg;
    var a := f(x);
    var id := u => u;
    g := id;  // error: cannot find a type for RHS that is assignable to LHS
  }

  function Id(x: int): nat
  {
    x
  }
}

module AssignmentToSetNat {
  method M(x0: set<int>, x1: set<int>, x2: set<int>, x3: set<int>)
  {
    var a: set<nat> := x0;  // error: types are not compatible
    a := x1;  // error: types are not compatible
    var z;
    z := var b: set<nat> := x2; b;  // error
    z := var b: set<nat> :| b == x3; b;  // this is a verification problem, but the type checker is happy
  }
  method M'(x0: set<int>, x1: set<int>, x2: set<int>, x3: set<int>, x4: set<int>)
  {
    var c: set<nat> :| c == x0;  // error
    c :| c == x1;  // error

    var g := new G;
    g.u := x2;  // error

    var y := F(x3);  // error

    M''(x4);  // error
  }
  method M''(x: set<nat>)

  function method F(q: set<nat>): set<int>
  function method F'(x: set<int>): set<nat>      // error (regarding result of F(x) in the body)
  {
    F
      (x)  // error (regaring argument to F)
  }

  class G {
    var u: set<nat>
  }

  function method Pf(n: set<nat>): set<int>
  function method Pg(x: set<int>): set<nat>

  method P(x: set<int>, f: set<nat> -> set<int>) returns (g: set<int> -> set<nat>)
    requires f.requires(x)  // error
  {
    var y := f(x);  // error
    g := z => z;  // error
  }
  method Q(x: set<int>) {
    var f := Pf;
    var g := Pg;
    var a := f(x);  // error
    var id := u => u;
    g := id;  // error
  }

  function Id(x: set<int>): set<nat>  // error
  {
    x
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

module Contravariance {
  method M0(a: int -> int, b: int -> nat, c: nat -> int, d: nat -> nat) returns (r: int -> int) {
    if {
      case true =>  r := a;
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;  // error
    }
  }
  method M1(a: int -> int, b: int -> nat, c: nat -> int, d: nat -> nat) returns (r: int -> nat) {
    if {
      case true =>  r := a;  // error
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;  // error
    }
  }
  method M2(a: int -> int, b: int -> nat, c: nat -> int, d: nat -> nat) returns (r: nat -> int) {
    if {
      case true =>  r := a;
      case true =>  r := b;
      case true =>  r := c;
      case true =>  r := d;
    }
  }
  method M3(a: int -> int, b: int -> nat, c: nat -> int, d: nat -> nat) returns (r: nat -> nat) {
    if {
      case true =>  r := a;  // error
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;
    }
  }
}
