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

  method P(x: int, f: nat ~> int) returns (g: int ~> nat)
    requires f.requires(x)  // error
  {
    var y := f(x);  // error
    g := z => z;  // error
  }
  method Q(x: int) {
    var f := Pf;
    var g := Pg;
    var a := f(x);  // error
    var id := u => u;
    g := id;  // error
  }

  function Id(x: int): nat
  {
    x  // error
  }
}

module AssignmentToSetNat {
  method M(x0: set<int>, x1: set<int>, x2: set<int>, x3: set<int>)
  {
    var a: set<nat> := x0;  // error
    a := x1;  // error
    var z;
    z := var b: set<nat> := x2; b;  // error
    z := var b: set<nat> :| b == x3; b;  // error
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
  function method F'(x: set<int>): set<nat>
  {
    F      // error (regarding result of F(x) in the body)
      (x)  // error (regaring argument to F)
  }

  class G {
    var u: set<nat>
  }

  function method Pf(n: set<nat>): set<int>
  function method Pg(x: set<int>): set<nat>

  method P(x: set<int>, f: set<nat> ~> set<int>) returns (g: set<int> ~> set<nat>)
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

  function Id(x: set<int>): set<nat>
  {
    x  // error
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
  method M0(a: int ~> int, b: int ~> nat, c: nat ~> int, d: nat ~> nat) returns (r: int ~> int) {
    if {
      case true =>  r := a;
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;  // error
    }
  }
  method M1(a: int ~> int, b: int ~> nat, c: nat ~> int, d: nat ~> nat) returns (r: int ~> nat) {
    if {
      case true =>  r := a;  // error
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;  // error
    }
  }
  method M2(a: int ~> int, b: int ~> nat, c: nat ~> int, d: nat ~> nat) returns (r: nat ~> int) {
    if {
      case true =>  r := a;
      case true =>  r := b;
      case true =>  r := c;
      case true =>  r := d;
    }
  }
  method M3(a: int ~> int, b: int ~> nat, c: nat ~> int, d: nat ~> nat) returns (r: nat ~> nat) {
    if {
      case true =>  r := a;  // error
      case true =>  r := b;
      case true =>  r := c;  // error
      case true =>  r := d;
    }
  }
}

module AssignSuchThat {
  type SmallInt = x | 0 <= x < 10
  method M() {
    var a: int :| a == 11;
    var b: SmallInt :| b == 11;  // error
  }
}

module SoftCasts {
  method P(n: nat) returns (g: int ~> nat)
  {
    if
    case true =>
      g := z => if z < 0 then -z else z;
    case true =>
      g := z => if z <= 0 then -z else z-1;
    case true =>
      g := z => if z < 0 then -z else z-1;  // error: may fail to return a nat
    case true =>
      g := z => n;
  }
}
