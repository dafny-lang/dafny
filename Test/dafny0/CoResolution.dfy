// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module TestModule {
  class TestClass {
    greatest predicate P(b: bool)
    {
      !b && Q(null)
    }

    greatest predicate Q(a: array<int>)
    {
      a == null && P(true)
    }

    greatest predicate S(d: set<int>)
    {
      this.Undeclared#[5](d) &&  // error: 'Undeclared#' is undeclared
      Undeclared#[5](d) &&  // error: 'Undeclared#' is undeclared
      this.S#[5](d) &&
      S#[5](d) &&
      S#[_k](d)  // error: _k is not an identifier in scope
    }

    greatest lemma CM(d: set<int>)
    {
      var b;
      b := this.S#[5](d);
      b := S#[5](d);
      this.CM#[5](d);
      CM#[5](d);
    }
  }
}

module GhostCheck0 {
  codatatype Stream<G> = Cons(head: G, tail: Stream)
  method UseStream0(s: Stream)
  {
    var x := 3;
    if (s == s.tail) {  // error: this operation is allowed only in ghost contexts
      x := x + 2;
    }
  }
}
module GhostCheck1 {
  codatatype Stream<G> = Cons(head: G, tail: Stream)
  method UseStream1(s: Stream)
  {
    var x := 3;
    if (s ==#[20] s.tail) {  // this seems innocent enough, but it's currently not supported by the compiler, so...
      x := x + 7;  // error: therefore, this is an error
    }
  }
}
module GhostCheck2 {
  codatatype Stream<G> = Cons(head: G, tail: Stream)
  ghost method UseStreamGhost(s: Stream)
  {
    var x := 3;
    if (s == s.tail) {  // fine
      x := x + 2;
    }
  }
}

module Mojul0 {
  class MyClass {
    greatest predicate D()
      reads this  // yes, greatest predicates can have reads clauses
    {
      true
    }

    greatest predicate NoEnsuresPlease(m: nat)
      ensures NoEnsuresPlease(m) ==> m < 100;  // error: a greatest predicate is not allowed to have an 'ensures' clause
    {
      m < 75
    }

    // Note, 'decreases' clauses are also disallowed on greatest predicates, but the parser takes care of that
  }
}

module Mojul1 {
  greatest predicate A() { B() }  // error: SCC of a greatest predicate must include only greatest predicates
  predicate B() { A() }

  greatest predicate X() { Y() }
  greatest predicate Y() { X#[10]() }  // error: X is not allowed to depend on X#

  greatest lemma M()
  {
    N();
  }
  greatest lemma N()
  {
    Z();
    W();  // error: not allowed to make co-recursive call to non-greatest lemma
  }
  lemma Z() { }
  lemma W() { M(); }

  greatest lemma G() { H(); }
  greatest lemma H() { G#[10](); }  // fine for greatest lemma/prefix-lemma
}

module CallGraph {
  // greatest lemma -> greatest predicate -> greatest lemma
  // greatest lemma -> greatest predicate -> prefix lemma
  greatest lemma CoLemma(n: ORDINAL)
  {
    var q := Q(n);  // error
    var r := R(n);  // error
  }

  greatest predicate Q(n: ORDINAL)
  {
    calc { 87; { CoLemma(n); } }  // error: this recursive call not allowed
    false
  }

  greatest predicate R(n: ORDINAL)
  {
    calc { 87; { CoLemma#[n](n); } }  // error: this recursive call not allowed
    false
  }

  // greatest lemma -> prefix predicate -> greatest lemma
  // greatest lemma -> prefix predicate -> prefix lemma
  greatest lemma CoLemma_D(n: ORDINAL)
  {
    var q := Q_D#[n](n);  // error
    var r := R_D#[n](n);  // error
  }

  greatest predicate Q_D(n: ORDINAL)
  {
    calc { 88; { CoLemma_D(n); } }  // error: this recursive call not allowed
    false
  }

  greatest predicate R_D(n: ORDINAL)
  {
    calc { 89; { CoLemma_D#[n](n); } }  // error: this recursive call not allowed
    false
  }

  // greatest predicate -> function -> greatest predicate
  // greatest predicate -> function -> prefix predicate
  greatest predicate P(n: ORDINAL)
  {
    G0(n)  // error
    <
    G1(n)  // error
  }

  function G0(n: ORDINAL): int
  {
    calc { true; { assert P(n); } }
    100
  }
  function G1(n: ORDINAL): int
  {
    calc { true; { assert P#[n](n); } }
    101
  }

  greatest lemma J()
  {
    var f := JF();  // error: cannot call non-greatest lemma recursively from greatest lemma
  }
  function JF(): int
  {
    J();
    5
  }
}

module CrashRegression {
  codatatype Stream = Cons(int, Stream)

  // The following functions (where A ends up being the representative in the
  // SCC and B, which is also in the same SCC, has no body) once crashed the
  // resolver.
  function A(): Stream
  {
    B()
  }
  function B(): Stream
    ensures A() == S();

  function S(): Stream
}

module AmbiguousTypeParameters {
  codatatype Stream<T> = Cons(T, Stream)

  function A(): Stream
  {
    B()
  }

  // Here, the type arguments to A and S cannot be resolved
  function B(): Stream
    ensures A() == S();

  function S(): Stream
}

