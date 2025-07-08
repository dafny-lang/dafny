// RUN: %testDafnyForEachResolver --expect-exit-code=2 --refresh-exit-code=4 "%s"

module UnusedTypeParametersOfSubtypeTypes {
  trait T<X> { }
  class D<X1> extends T<(int, seq<X1>)> { }
  type F<X2, Unused> = d: D<X2> | true witness * // the legacy resolver treats F as a reference type, and bogusly wants all parameters to be equal in order to have type compatibility

  method Test<X>(f: F<X, X>, g: F<X, int>) {
    if * {
      var h: F<X, X>;
      h := f;
      h := g;
    } else {
      var h: F<X, int>;
      h := g;
      h := f;
    }

    var s0: seq<F<X, X>> := [f, f, f];
    var s1: seq<F<X, int>> := [g, g, g];
    if * {
      s0 := s1;
    } else {
      s1 := s0;
    }
  }

  method Test1<X>(f: F<X, X>, g: F<X, int>) {
    var c0: C<F<X, int>> := new C<F<X, int>>(g);
    var c1: C<F<X, X>> := new C<F<X, X>>(f);

    // The resolver should treat the following three consistently. That is, it should either disallow all three
    // or allow all three. (It allows all three.) The verifier should also treat the three consistently (which,
    // for the way unused type parameters in subset types are currently treated, is to say that all three branches
    // causes a verification error).
    if
    case true =>
      var b: bool := c1 is C<F<X, int>>;
      assert b; // error: this may not hold
    case true =>
      c0 := c1; // error: RHS value not assignable to LHS
    case true =>
      c0 := c1 as C<F<X, int>>; // error: precondition of "as" may not be satisfied
  }

  method Test2<X>(f: F<X, X>, g: F<X, int>) {
    var c0: C<F<X, int>> := new C<F<X, int>>(g);
    var c1: C<F<X, X>> := new C<F<X, X>>(f);

    // The resolver should treat the following three consistently. That is, it should either disallow all three
    // or allow all three. (It allows all three.) The verifier should also treat the three consistently (which,
    // for the way unused type parameters in subset types are currently treated, is to say that all three branches
    // causes a verification error).
    if
    case true =>
      var b: bool := c0 is C<F<X, X>>;
      assert b; // error: this may not hold
    case true =>
      c1 := c0; // error: RHS value not assignable to LHS
    case true =>
      c1 := c0 as C<F<X, X>>; // error: precondition of "as" may not be satisfied
  }

  class C<Y> {
    var y: Y
    constructor (y: Y) {
      this.y := y;
    }
  }
}
