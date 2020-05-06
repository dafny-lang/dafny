// RUN: %dafny /env:0 /rprint:- /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  trait Tr<X> {
    function F(x: X): int { 15 }
  }

  class Cl<Y> extends Tr<Y> {
    lemma M() {
      var v := this;  // Cl<Y>
      var u: Tr := this;  // Tr<Y>

      var f := v.F;  // Y -> int
      var g := this.F;  // Y -> int
    }
  }
}

module M1 {
  trait Tr<X(0)> {
    var w: X
  }

  class Cl<Y> extends Tr<(Y,Y)> {
  }

  lemma M(c: Cl<int>) {
    var x := c.w;  // (int, int)
  }
}

module M2 {
  trait Tr<X, W> {
    function method F(x: X, w: W): bv10 { 15 }
  }

  class Cl<Y> extends Tr<(Y,Y), real> {
  }

  lemma M(c: Cl<int>) {
    var aa;  // (int, int)
    var bb;  // real
    var u := c.F(aa, bb);  // bv10
  }
}

module M3 {
  trait Tr<X, W> {
    function method F(x: X, w: W): bv10 { 15 }
  }

  class Cl<Y> extends Tr<(Y,Y), real> {
    function method H(y: Y): bv10 {
      F((y, y), 5.0)
    }
  }
}

module M4 {
  trait Tr<X> {
    method M<A>(a: A, x: (X,A))
  }
  class Cl<Y> extends Tr<Y> {
    method M<B>(a: B, x: int) { }  // error: type of x is int instead of the expected (Y, B)
  }
}

module NewMustMentionAClassName {
  trait Tr<X> {
    method Make() { }
  }

  class A extends Tr<int> { }
  class B extends Tr<int> { constructor () { } }
  class C<G> extends Tr<G> { }
  class D<G> extends Tr<G> {
    constructor () { }
    constructor Init() { }
  }

  type ASynonym = A
  type DSynonym<H> = D<(H, int)>
  type ObjectSynonym = object
  type ObjectWithConstraint = o: object | true

  method M() {
    var a0 := new A;
    var a1 := new A?;  // error: expects A, not A?
    var a2 := new ASynonym;  // error: must mention class name directly, not a type

    var b0 := new B();
    var b1 := new B?();  // error: expects B, not B?

    var c0 := new C<A>;
    var c1 := new C?<A>;  // error: expects C, not C?
    var c2 := new C<A?>;
    var c3 := new C?<A?>;  // error: expects C, not C?

    var d0 := new D<A>();
    var d1 := new D?<A>();  // error: expects D, not D?
    var d2 := new D<A?>();
    var d3 := new D?<A?>();  // error: expects D, not D?
    var d4 := new D<A>.Init();
    var d5 := new D?<A>.Init();  // error: expects D, not D?
    var d6 := new D<A?>.Init();
    var d7 := new D?<A?>.Init();  // error: expects D, not D?
    var d8 := new DSynonym<A?>();  // error: must mention class name directly, not a type
    var d9 := new DSynonym<A?>.Init();  // error: must mention class name directly, not a type

    var o0 := new object;
    var o1 := new object?;  // error: expects object, not object?
    var o2 := new ObjectSynonym;  // error: must denote a class directly
    var o3 := new ObjectWithConstraint;  // error: must denote a class directly

    var arr0 := new array<int>;  // weird, but allowed
    var arr1 := new array?<int>;  // error: expects array, not array?

    var i0 := new int;  // error: Come on! int? Whazzup with that?

    var t0 := new Tr<int>;  // error: not a class
    var t1 := new Tr?<int>;  // error: not a class
    var t2 := new Tr<int>.Make();  // error: not a class
    var t3 := new Tr?<int>.Make();  // error: not a class
  }
}

module DuplicateParents {
  trait A { var data: int }
  trait B { var data: int }
  trait C<X> { }

  type IntSynonym = int
  type Even = x | x % 2 == 0

  class P extends A, A, B, A { }  // error: A and B both contain a member "data"
  class Q extends C<int>, C<int> { }
  class R extends C<IntSynonym>, C<int> { }
  class S extends C<Even>, C<int> { }  // error: cannot extend C in different ways
  class T extends C<int>, C<int>, C<int>, C<real>, C<int>, C<Even> { }  // error: cannot extend C in different ways
}

module DuplicateInheritedMembers {
  trait A {
    var data: int
  }
  trait B {
    var data: int
  }
  trait C {
    var data: real
  }
  trait D {
    function data(): int { 5 }
  }

  class P extends B, A { }  // error: A and B both contain a member "data"
  class Q extends C, A { }  // error: A and B both contain a member "data"
  class R extends D, A { }  // error: A and B both contain a member "data"
}

module StaticMembers {
  trait Tr {
    static const Cnst: object  // error: the type of this static const requires an initializing expression

    // the following static members must also be given bodies, but that's checked by the compiler (see TraitCompileErrors.dfy)
    static function method Func(): int
    static method Method()
    static twostate function TwoF(): int
    static twostate lemma TwoL()
    static inductive predicate P()
    static copredicate Q()
    static inductive lemma IL()
    static colemma CL()
  }
}
