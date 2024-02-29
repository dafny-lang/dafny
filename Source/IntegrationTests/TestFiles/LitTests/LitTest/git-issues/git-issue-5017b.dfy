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
    reveal a.Valid(); // error: cannot reveal (no body)
  }

  method TestB(b: B) {
    reveal b.Valid();
  }

  method TestC(c: C) {
    reveal c.Valid();
  }
}

module RevealErrorMessages {
  trait A {
    opaque predicate Valid()
    function TransparentFunction(): int { 3 }
    const m: int := 10
    opaque const n: int := 10
    opaque const o: int
    method Method() { }
    opaque function WithBody(x: int): int { x }

    method TestReveal() {
      reveal UnknownFunction(); // error: UnknownFunction unresolved
      reveal UnknownFunction; // error: UnknownFunction unresolved
      reveal Method(); // error: Method unresolved
      reveal Method; // error: Method unresolved
      reveal m; // error: m unresolved
      reveal n;
      reveal o;
      reveal Valid(); // error: Valid unresolved
      reveal Valid; // error: Valid unresolved
      reveal WithBody();
      reveal WithBody; // error: missing parens
    }
  }

  method TestA(a: A) {
    reveal x.Valid(); // error: 'x' is unresolved
    reveal a.UnknownFunction(); // error: UnknownFunction unresolved
    reveal a.UnknownFunction; // error: UnknownFunction unresolved
    reveal a.Method(); // error: cannot reveal a method
    reveal a.Method;
    reveal a.m; // error: cannot reveal (not opaque)
    reveal a.n;
    reveal a.o;
    reveal a.Valid(); // error: cannot reveal (no body)
    reveal a.Valid; // error: cannot reveal (no body)
    reveal a.WithBody();
    reveal a.WithBody; // error: missing parens

    reveal A.WithBody(); // error: WithBody not found (as static member) in A
  }
}
