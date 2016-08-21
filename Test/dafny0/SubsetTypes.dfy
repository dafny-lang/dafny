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
  /*
  method P(x: int, f: nat -> int) returns (g: int -> nat) {
    var y := f(x);
    g := z => z;
  }
  method Q(x: int) {
    var f := Pf;  // BUG: this is not supposed to happen, since it gives f the type nat->int
    var g := Pg;  // BUG: this is not supposed to happen, since it gives g the type int->nat
    var a := f(x);  // error
    var id := u => u;
    g := uu;  // BUG: there's a missing check here that the RHS (int -> int) is really a LHS (int -> nat)
  }
   */

  function Id(x: int): nat
  {
    x  // error
  }
}
/*
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
    F
      (x)  // error (x2)
  }

  class G {
    var u: set<nat>
  }

  function method Pf(n: set<nat>): set<int>
  function method Pg(x: set<int>): set<nat>
  /*
  method P(x: set<int>, f: set<nat> -> set<int>) returns (g: set<int> -> set<nat>) {
    var y := f(x);
    g := z => z;
  }
   */
  method Q(x: set<int>) {
    var f := Pf;  // BUG: this is not supposed to happen, since it gives f the type set<nat>->set<int>
    var g := Pg;  // BUG: this is not supposed to happen, since it gives g the type set<int>->set<nat>
    var a := f(x);  // error
    g := u => u;  // BUG: there's a missing check here that the return value is a set<nat>
  }

  function Id(x: set<int>): set<nat>
  {
    x  // error
  }
}
 */
