// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --general-traits=datatype

module True {
  trait A {
    ghost predicate Valid()
  }

  trait B extends A {
    ghost opaque predicate Valid() { true }
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
}

module X {
  trait A {
    ghost predicate Valid(w: bool)
  }

  trait B extends A {
    ghost opaque predicate Valid(x: bool) { x }
  }

  method TestByRequires(b: B, y: bool)
    requires b.Valid(y)
  {
    var a: A := b;
    assert a.Valid(y);
  }

  method TestByReveal(b: B, y: bool) {
    var a: A := b;
    assert a.Valid(y) by { // error: assertion violation
      reveal b.Valid();
    }
  }
}

module Parameters {
  trait A {
    ghost predicate P<T>(t: T)
  }

  trait B extends A {
    ghost opaque predicate P<T>(t: T) { t == t }
  }


  method TestByRequires(b: B)
    requires b.P(5)
  {
    var a: A := b;
    assert a.P(5);
  }

  method TestByRequires'(b: B)
    requires b.P(6)
  {
    var a: A := b;
    assert a.P(5); // error: assertion violation
  }

  method TestByRequires''(b: B)
    requires b.P(true)
  {
    var a: A := b;
    assert a.P(5); // error: assertion violation
  }


  method TestByReveal(b: B) {
    var a: A := b;
    assert a.P(5) by {
      reveal b.P();
    }
  }

  method TestByReveal'(b: B) {
    var a: A := b;
    assert a.P(true) by {
      reveal b.P();
    }
  }
}

module StayOpaque {
  trait A {
    opaque predicate Valid()
  }

  trait B extends A {
    opaque predicate Valid() { true }
  }

  trait C extends A {
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
