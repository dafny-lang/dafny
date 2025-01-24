// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Datatype {
  trait A {
    opaque predicate Valid()
  }

  datatype B extends A = B {
    opaque predicate Valid() { true }
  }

  datatype C extends A = C {
    opaque predicate Valid() { true }
  }

  method TestByRequires(b: B)
    requires b.Valid()
  {
    var a: A := b;
    assert a.Valid();
  }

  method TestByReveal(b: B) {
    var a: A := b;
    assert a.Valid() by {
      reveal b.Valid();
    }
  }

  method TestIndependence0(b: B, c: C) {
    var a: A := b;
    assert b.Valid() by { // error: revealing for C should not affect B
      reveal c.Valid();
    }
  }

  method TestIndependence1(b: B, c: C) {
    var a: A := b;
    assert a.Valid() by { // fine: revealing for C also reveals for all A's
      reveal c.Valid();
    }
  }
}

module Class {
  trait A {
    opaque predicate Valid()
  }

  class B extends A {
    opaque predicate Valid() { true }
  }

  class C extends A {
    opaque predicate Valid() { true }
  }

  method TestByRequires(b: B)
    requires b.Valid()
  {
    var a: A := b;
    assert a.Valid();
  }

  method TestByReveal(b: B) {
    var a: A := b;
    assert a.Valid() by {
      reveal b.Valid();
    }
  }

  method TestIndependence0(b: B, c: C) {
    var a: A := b;
    assert b.Valid() by { // error: revealing for C should not affect B
      reveal c.Valid();
    }
  }

  method TestIndependence1(b: B, c: C) {
    var a: A := b;
    assert a.Valid() by { // fine: revealing for C also reveals for all A's
      reveal c.Valid();
    }
  }
}
