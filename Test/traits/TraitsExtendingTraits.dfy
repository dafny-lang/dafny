// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module TheBasics {
  trait A {
  }
  trait B {
  }
  trait C {
  }
  trait D {
  }
  trait X extends A, B {
  }
  trait Y extends C {
  }
  class K extends X, Y, D {
  }
}

module ForbiddenCycles {
  // The following two traits would form a cycle
  trait A extends B { }  // error: cycle
  trait B extends A { }

  trait SelfLoop extends SelfLoop { }  // error: cycle

  trait K<Y> extends M<Y> { }  // error: cycle
  trait L<X> extends K<(X,int)> { }
  trait M<U> extends L<U --> int>, B { }

  trait P extends B { }
}

module DuplicateMembers {
  trait A {
    var data: int
    var karljohan: real
  }
  trait Q {
    var mumble: int
  }
  trait B {
    var data: int
    var sopp: int
    var fluga: real
  }
  trait C extends A, Q {
    var fluga: real
    var svamp: real
  }
  trait D extends B {
    var karljohan: real
    var svamp: real
  }
  trait X extends C, D {  // error (x4): duplicate members: data, fluga, karljohan, svamp
  }

  class J extends Y, D {  // error: duplicate member "sopp"
  }
  trait Y {
    function sopp(): real
  }
  class K extends D, Y {  // error: duplicate member "sopp"
  }
  class L extends Y, D {  // error: duplicate member "sopp"
  }

  class Diamond extends Elva, Tolv {
  }
  trait Elva extends Tio {
    function balalaika(): nat
  }
  trait Tolv extends Tio {
    function banjo(): nat
  }
  trait Tio {
    function munspel(): nat
    function banjo(): nat
    function balalaika(): nat
  }

  class InheritedOverrideAndOriginal extends Left, Right {
    // everything is fine
  }
  trait Left {
    method M() { }  // this is an override
  }
  trait Right {
  }
  trait Orig {
    method M()
  }

  class TwoOverrides extends Left2, Right2 {  // error: inherits two unrelated overrides of M
  }
  trait Left2 {
    method M() { }  // this is an override
  }
  trait Right2 {
    method M() { }  // this is an override
  }
  trait Orig2 {
    method M()
  }
}
