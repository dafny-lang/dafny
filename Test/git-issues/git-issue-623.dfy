// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ----- example reported in Issue 623

module M1 {
  export Abs
    provides M, T
  export Conc
    provides M, MyClass
    reveals T

  class MyClass {
  }

  type T = MyClass

  lemma M(f: T ~> bool)
    requires forall t :: f.requires(t) ==> f(t)  // regression test: this once crashed during checking of M2
  { }
}

module M2 {
  import M1`Abs

  method K(t: M1.T) {
  }
}

module M3 {
  import M1`Conc

  method K(t: M1.T) {
  }
}

// ----- example reported in Issue 150

module N1 {
  export
    provides T, Equal, Foo

  type T(==) = seq<real>

  ghost predicate Equal(u: T, v: T)
  {
    u == v
  }

  lemma Foo()
    ensures forall u, v :: Equal(u, v) ==> u == v  // regression test: this once crashed during checking of N2
  { }
}

module N2 {
  import N1

  lemma Bar(u: N1.T, v: N1.T)
    requires N1.Equal(u, v)
  {
    N1.Foo();
    assert u == v;
  }
}


// ------------------- additional examples

module Library {
  export
    provides W, P, X, Q
    provides M0, M1

  type W = MyTrait
  trait MyTrait {
  }
  ghost predicate P(u: W)

  type X = MyClass
  class MyClass extends MyTrait {
  }
  ghost predicate Q(x: X)

  lemma M0()
    requires forall t :: P(t)
  { }
  lemma M1()
    requires forall t :: Q(t)
  { }

  lemma Private0()
    requires forall t :: P(t) && Q(t)  // error: t is inferred as MyTrait, so can't prove that Q(t) is well-formed
  { }
  lemma Private1()
    requires forall t :: Q(t) && P(t)  // error: t is inferred as MyTrait, so can't prove that Q(t) is well-formed
  { }
}

module Client {
  import Library

  method K()
    requires forall t :: Library.P(t)
    requires forall t :: Library.Q(t)
  {
  }
}
