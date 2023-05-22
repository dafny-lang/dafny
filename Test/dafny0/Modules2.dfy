// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class C {
    constructor () { }
    var f: int;
  }
  datatype D = E(int) | F(int)
  ghost function f(n:nat): nat
}
module B {
  class C {
    var f: int;
  }
  datatype D = E(int) | F(int)
  ghost function f(n:nat): nat
}
module Test {
  import opened A // nice shorthand for import opened A = A; (see below)
  method m() {
    var c := new C();   // fine, as A was opened
    var c' := new A.C();// also fine, as A is bound
    var i := 43;
    var d  := E(i);     // these all refer to the same value
    var d' := A.E(i);
    var d'':= A.D.E(i);
    assert d == d' == d'';
    assert f(3) >= 0; // true because f(x): nat
    assert A._default.f(3) >= 0;
  }
}

abstract module Test2 {
  import opened B : A
  method m() {
    var c := new C();   // fine, as A was opened
    var c' := new B.C();// also fine, as A is bound
    assert B.f(0) >= 0;
  }
}

module Test3 {
  import opened A
  import opened B // everything in B clashes with A
  method m() {
    var c := new C();    // bad, ambiguous between A.C and B.C
    var c' := new A.C(); // good: qualified.
    var i := 43;
    var d  := E(i);     // bad, as both A and B give a definition of E
    var d' := D.E(i);   // bad, as D is still itself ambiguous.
    var d'':= B.D.E(i); // good, just use the B version
    assert f(3) >= 0;   // bad because A and B both define f statically.
  }
}

module Test4 {
  import A = A // good: looks strange, but A is not bound on the RHS of the equality
  import B // the same as the above, but for module B
}
