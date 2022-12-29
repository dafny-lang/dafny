// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
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
  class C ... {
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
  class C ... {
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
  class C ... {
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

module FineToRefine {
  type T
}

module TryToRefine refines FineToRefine {
  type T = int
}

// ------------- type parameter variance and characteristics -----------

module OrigA {
  type T<A,B>
}
module TpA refines OrigA {
  type T<C,D,E>  // error: change in number of type parameters
}

module OrigB {
  type T<A,B(0),C(00),D,E(0),F(00),G,H(0),I(00)>
}
module TpB refines OrigB {
  type T<A,B,C,D(0),E(0),F(0),G(00),H(00),I(00)>  // error (x6): change in (0)/(00) requirements
}

module OrigC {
  type T<A,B(==)>
}
module TpC refines OrigC {
  type T<A(==),B>  // error (x2): change in (==) requirement
}

module OrigD {
  type T<+A,!B,-C,D,E,F>
}
module TpD refines OrigD {
  type T<!A,-B,+C,!D,-E,+F>  // error (x5): change in variance
}

module OrigE {
  type T<+A,!B,-C,D,E,F,W,X(==),Y,Z(0)>
  }
module TpE refines OrigE {
  class T<!A,-B,+C,!D,-E,+F,W(==),X,Y(0),Z>  // error (x9): various changes
  {
  }
}

module OrigF {
  class T<+A,!B,-C,D,E,F,W,X(==),Y,Z(0)>
  {
  }
}
module TpF refines OrigF {
  class T<!A,-B,+C,!D,-E,+F,W(==),X,Y(0),Z>  // error (x9): various changes
  ... {
  }
}

module OrigG {
  type T<+A,!B,-C,D,E,F,W,X(==),Y,Z(0)>
}
module TpG refines OrigG {
  datatype T<!A,-B,+C,!D,-E,+F,W(==),X,Y(0),Z> = Yup  // error (x9): various changes
}

module OrigH {
  type T<+A,!B,-C,D,E,F,W,X(==),Y,Z(0)>
}
module TpH refines OrigH {
  type T<!A,-B,+C,!D,-E,+F,W(==),X,Y(0),Z> = int  // error (x9): various changes
}

module OrigI {
  type T<+A,!B,-C,D,E,F,W,X(==),Y,Z(0)>
}
module TpI refines OrigI {
  type T<!A,-B,+C,!D,-E,+F,W(==),X,Y(0),Z> = u | 0 <= u  // error (x9): various changes
}

module OrigJ {
  iterator S<A>()
  iterator T<+A,!B,-C,D,E,F,W,X(==),Y,Z(0)>()
  {
  }
}
module TpJ refines OrigJ {
  iterator S ...


  iterator T
  ... {
  }
}
