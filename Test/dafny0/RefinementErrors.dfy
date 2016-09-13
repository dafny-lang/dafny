// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class C {
    method M(y: int) returns (x: int)
    {
      x := 6;
    }

    var abc: bool;
    var xyz: bool;

    function method F<A,B,C>(x: int, y: A, z: set<C>, b: bool): B

    function G(): int  // uninterpreted for now
    function H(): int  // uninterpreted for now

    method BodyLess(y: bool, k: seq<set<object>>) returns (x: int)
    method FullBodied(x: int) returns (y: bool, k: seq<set<object>>)
    {
    }
  }
}

module B refines A {
  class C {
    var k: int;
    method M(y: int) returns (x: int)
      requires 0 <= y;  // error: cannot add a precondition
      modifies this;  // error: cannot add a modifies clause
      ensures 0 <= x;  // fine

    predicate abc()  // error: cannot replace a field with a predicate
    var xyz: bool;  // error: ...or even with another field

    function F   // error: cannot replace a "function method" with a "function"
        <C,A,B>  // error: different list of type parameters
        (x: int, y: A, z: seq<C>,  // error: different type of parameter z
         k: bool)  // error: different parameter name
        : B

    function G(): int
    { 12 }  // allowed to add a body

    method BodyLess(y: bool, k: seq<set<object>>) returns (x: int)
    {  // yes, can give it a body
    }
    method FullBodied(x: int) returns (y: bool, k: seq<set<object>>)
    {
    }
  }
}

module BB refines B {
  class C {
    function method G(): int  // error: allowed to make a function into a function method
    function method H(): int  // ...unless this is where the function body is given
    { 10 }
  }
}

module Forall0 {
  class C {
    var a: int
    method M()
      modifies this
    {
    }
    lemma Lemma(x: int)
    {
    }
  }
}
module Forall1 refines Forall0 {
  class C {
    var b: int
    method M...
    {
      forall x { Lemma(x); }  // allowed
      var s := {4};
      forall x | x in s ensures x == 4 { }  // allowed
      forall x {  // allowed
        calc {
          x in s;
        ==
          x == 4;
        }
      }
      forall c: C | c in {this} {
        c.b := 17;  // allowed
      }
      forall c: C | c in {this} {
        c.a := 17;  // error: not allowed to update previously defined field
      }
    }
  }
}

protected module CannotRefine {
  type T
}

module TryToRefine refines CannotRefine { // error
  type T = int
}

// ------------- visibility checks -------------------------------

