// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --general-traits=datatype

module Opaque {
  trait A {
    predicate Valid()
  }

  trait B {
    opaque predicate Valid() { true }
  }

  trait C {
    opaque predicate Valid()
  }


  trait K0 extends A {
    predicate Valid()
  }
  trait K1 extends A {
    opaque predicate Valid()
  }
  trait K2 extends A {
    predicate Valid() { true }
  }
  trait K3 extends A {
    opaque predicate Valid() { true }
  }

  trait L0 extends B {
    predicate Valid() { true } // error: B.Valid already has a body
  }
  trait L1 extends B {
    opaque predicate Valid() { true } // error: B.Valid already has a body
  }

  trait M0 extends C {
    predicate Valid() // error: must be opaque (since it is in C)
  }
  trait M1 extends C {
    opaque predicate Valid()
  }
  trait M2 extends C {
    predicate Valid() { true } // error: must be opaque (since it is in C)
  }
  trait M3 extends C {
    opaque predicate Valid() { true }
  }


  datatype W0 extends A = W0 {
    predicate Valid() { true }
  }
  class W1 extends A {
    predicate Valid() { true }
  }

  datatype X0 extends A = X0 {
    opaque predicate Valid() { true }
  }
  class X1 extends A {
    opaque predicate Valid() { true }
  }

  datatype Y0 extends C = Y0 {
    predicate Valid() { true } // error: must be opaque (since it is in C)
  }
  class Y1 extends C {
    predicate Valid() { true } // error: must be opaque (since it is in C)
  }

  datatype Z0 extends C = Z0 {
    opaque predicate Valid() { true }
  }
  class Z1 extends C {
    opaque predicate Valid() { true }
  }
}

module StayOpaque {
  trait A {
    opaque predicate Valid()
  }

  datatype B extends A = B {
    opaque predicate Valid() { true }
  }

  class C extends A {
    opaque predicate Valid() { true }
  }

  method TestA(a: A) {
    reveal a.Valid(); // error: nothing to reveal
  }

  method TestB(b: B) {
    reveal b.Valid();
  }

  method TestC(c: C) {
    reveal c.Valid();
  }
}
