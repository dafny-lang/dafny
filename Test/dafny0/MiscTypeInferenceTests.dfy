// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// All of the examples in this file should type check (but some produce
// verification errors). The examples were some of the ones used during
// the design of the type-inference heuristics.

module ErrorLocation {
  type neg = x | x < 0 witness -1
  predicate P(n: nat) { true }
  predicate Q(y: neg) { true }
  lemma Test()
  {
    assert forall x :: (0 <= x ==> P(x)) && (100 < x ==> Q(x));  // error:
    //                                                ^ This is where the error should show
  }
}

module ArrowVariance {
  method Q() returns (f: int -> int, g: int ~> nat)
  {
    if * {
      assume forall x :: g.requires(x) && g.reads(x) == {};
      // When reads and requires clauses used to take type arguments,
      // the following assignment used to result in an error.
      // The error occurred as follows: to prove that g can be assigned
      // to f, Boogie would check that g is a total function from int to int:
      //    assert $Is(g#0, Tclass._System.___hTotalFunc1(TInt, TInt));
      // This can be proved if we know that for all x of type int,
      // g.requires(x) is true. Since the translation of the requires clause
      // used to take type arguments (corresponding to the function's parameter
      // and return types), this would mean proving that
      // g.requires(int, int, x) is true. However, since we only know that
      // g.requires(int, nat, x) is true, we could not prove it.
      // Now that we removed type arguments from the requires and reads clauses,
      // the check can pass. This should not be a problem since typechecking is still
      // performed by Dafny.
      f := g;
    } else if * {
      assume forall x :: 0 <= f(x);
      g := f;  // error: (it would be nice if this didn't produce an error)
    } else if * {
      // The following is a workaround for the issue above
      var h: int ~> int := g;
      assume forall x :: g.requires(x) && g.reads(x) == {};
      assume forall x :: h.requires(x) && h.reads(x) == {};
      f := h;
    } else {
      // The following is another workaround for the issue above, this time with no run-time overhead
      ghost var h: int ~> int := g;
      assume forall x :: g.requires(x) && g.reads(x) == {};
      assume forall x :: h.requires(x) && h.reads(x) == {};
      f := g;
    }
  }
}

module MemberCall {
  class Ref<A(0)> {
    var val: A
  }
  method Nope() {
    var f := new Ref<int --> bool>;
    assert f.val(0);  // error (x2): precondition and assert
  }
}

module HomegrownNonNullType {
  class C { var u: int }
  function method F(): C
  type MyNonNullC = c: C? | c != null witness F()

  method M(c: MyNonNullC)
  {
    assert c != null;
  }

  method P(c: MyNonNullC)
  {
    var n := null;
    assert c != n;
  }
}

module NullLiterals {
  class Node { }
  method Main() {
    M({});
    var x := new Node;
    M'(x);
  }
  method M(S: set<Node?>) {
    var n := null;
    var b: bool;
    b := n in S;
  }
  method M'(x: Node) {
    var b;
    b := x == null;  // warning (with hint)
  }
  method M''(x: Node) {
    var b;
    var n := null;  // the type of n is inferred to be a possibly null type
    b := x == n;  // no warning, since the literal null is not used in the comparison
  }

  method P(s: set<Node>)
  {
    assert null !in s;  // warning -- good (but should not give a verification error)
  }
}

module XJ {
  predicate method Z(z: real) { z == 3.14 }
  class Cell { var data: int }
  method D(k: int, seven: Cell)
    requires seven.data == 7
  {
    var y: Cell :| y.data == 7;
    var y': Cell? :| y' == null || y'.data == 8;
    var y'': Cell :| true;

    var y'3: Cell :| k == 113;  // error: cannot establish existence of LHS
    var y'4: Cell :| false;  // error: cannot establish existence of LHS
    var z: real :| Z(z);
  }
}

module Numerics {
  type neg = x: int | x < 0 witness -8

  method IntLike() returns (ks: set<nat>, ns: set<neg>, z: bool) {
    var y := -8;
    z := y in ks;

    z := -8 in ks;
    z := 8 in ns;
  }
}

module SetCovariance {
  class Node { }
  method Test(F: set<object>, S: set<Node>)
  {
    var b := F == S;
  }
}

module Lists_NoVariance {
  datatype List<G> = Nil | Cons(G, List<G>)
  method Prepend(xs: List<nat>) returns (ys: List<nat>)
  {
    ys := Cons(55, xs);  // fine
  }
  method BadPrepend(xs: List<nat>) returns (ys: List<nat>)
  {
    ys := Cons(-55, xs);  // error: the error is the use of -55, not the assignment of ys
  }
}

module Lists_CoVariance {
  datatype List<+G> = Nil | Cons(G, List<G>)
  method Prepend(xs: List<nat>) returns (ys: List<nat>)
  {
    ys := Cons(55, xs);  // fine
  }
  method BadPrepend(xs: List<nat>) returns (ys: List<nat>)
  {
    ys := Cons(-55, xs);  // error: the error is the use of -55, not the assignment of ys
  }
}
