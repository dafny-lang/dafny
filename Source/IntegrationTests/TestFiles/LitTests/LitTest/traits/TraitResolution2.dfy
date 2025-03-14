// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M0 {
  trait TrX<X> {
    ghost function F(x: X): int { 15 }
  }
  trait Tr<X> extends TrX<X> {
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
  trait TrX<X(0)> extends object {
    var w: X
  }
  trait Tr<X(0)> extends TrX<X> {
  }
  class Cl<Y(0)> extends Tr<(Y,Y)> {
  }

  lemma M(c: Cl<int>) {
    var x := c.w;  // (int, int)
  }
}

module M2 {
  trait TrX<X, W> {
    function F(x: X, w: W): bv10 { 15 }
  }
  trait Tr<X, W> extends TrX<X, W> {
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
  trait TrX<X, W> {
    function F(x: X, w: W): bv10 { 15 }
  }
  trait Tr<X, W> extends TrX<X, W> {
  }
  class Cl<Y> extends Tr<(Y,Y), real> {
    function H(y: Y): bv10 {
      F((y, y), 5.0)
    }
  }
}
module M4 {
  trait TrX<X> {
    method M<A>(a: A, x: (X,A))
  }
  trait Tr<X> extends TrX<X> {
  }
  class Cl<Y> extends Tr<Y> {
    method M<B>(a: B, x: int) { }  // error: type of x is int instead of the expected (Y, B)
  }
}

module NewMustMentionAClassName {
  trait TrX<X> {
    method Make() { }
  }
  trait Tr<X> extends TrX<X>, object { }
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

module CannotRedeclareMembers {
  trait Tr {
    var civ: object
    ghost var giv: object
    const cic: object
    ghost const gic: object
    static const csc: object
    ghost static const gsc: object

    function cif0(): int
    ghost function gif0(): int
    function cif1(): int
    ghost function gif1(): int
    function cif2(): int { 5 }
    ghost function gif2(): int { 5 }
    function cif3(): int { 5 }
    ghost function gif3(): int { 5 }

    static ghost function csf0(): int
    static ghost function gsf0(): int
    static ghost function csf1(): int
    static ghost function gsf1(): int
    static ghost function csf2(): int { 2 }
    static ghost function gsf2(): int { 2 }
    static ghost function csf3(): int { 2 }
    static ghost function gsf3(): int { 2 }

    method cim0()
    ghost method gim0()
    method cim1()
    ghost method gim1()
    method cim2() { }
    ghost method gim2() { }
    method cim3() { }
    ghost method gim3() { }

    static method csm0()
    static ghost method gsm0()
    static method csm1()
    static ghost method gsm1()
    static method csm2() { }
    static ghost method gsm2() { }
    static method csm3() { }
    static ghost method gsm3() { }
  }
  trait TrY extends Tr {
  }
  class Cl extends TrY {
    var civ: object  // error: cannot redeclare
    ghost var giv: object  // error: cannot redeclare
    const cic: object  // error: cannot redeclare
    ghost const gic: object  // error: cannot redeclare
    static const csc: object  // error: cannot redeclare
    ghost static const gsc: object  // error: cannot redeclare

    function cif0(): int
    ghost function gif0(): int
    function cif1(): int { 5 }
    ghost function gif1(): int { 5 }
    function cif2(): int  // error: cannot redeclare member that already has a body
    ghost function gif2(): int  // error: cannot redeclare member that already has a body
    function cif3(): int { 5 }  // error: cannot redeclare member that already has a body
    ghost function gif3(): int { 5 }  // error: cannot redeclare member that already has a body

    static ghost function csf0(): int  // error: cannot redeclare static member
    static ghost function gsf0(): int  // error: cannot redeclare static member
    static ghost function csf1(): int { 2 }  // error: cannot redeclare static member
    static ghost function gsf1(): int { 2 }  // error: cannot redeclare static member
    static ghost function csf2(): int  // error: cannot redeclare static member
    static ghost function gsf2(): int  // error: cannot redeclare static member
    static ghost function csf3(): int { 2 }  // error: cannot redeclare static member
    static ghost function gsf3(): int { 2 }  // error: cannot redeclare static member

    method cim0()
    ghost method gim0()
    method cim1() { }
    ghost method gim1() { }
    method cim2()  // error: cannot redeclare member that already has a body
    ghost method gim2()  // error: cannot redeclare member that already has a body
    method cim3() { }  // error: cannot redeclare member that already has a body
    ghost method gim3() { }  // error: cannot redeclare member that already has a body

    static method csm0()  // error: cannot redeclare static member
    static ghost method gsm0()  // error: cannot redeclare static member
    static method csm1() { }  // error: cannot redeclare static member
    static ghost method gsm1() { }  // error: cannot redeclare static member
    static method csm2()  // error: cannot redeclare static member
    static ghost method gsm2()  // error: cannot redeclare static member
    static method csm3() { }  // error: cannot redeclare static member
    static ghost method gsm3() { }  // error: cannot redeclare static member
  }
}

module MemberMismatch {
  trait AAA {
    function F(): bool
    ghost function G(): bool
    twostate function H(): bool

    method M()
    ghost method N()
    lemma L()
    twostate lemma K()

    least predicate P()
    greatest predicate Q()
    least lemma R()
    greatest lemma S()
  }
  trait A3 extends AAA {
  }
  class SwitchGhostStatus extends A3 {
    ghost function F(): bool  // error: ghost mismatch
    function G(): bool  // error: ghost mismatch
    twostate function H(): bool

    ghost method M()  // error: ghost mismatch
    method N()  // error: ghost mismatch
    lemma L()
    twostate lemma K()

    least predicate P()
    greatest predicate Q()
    least lemma R()
    greatest lemma S()
  }

  class SwitchLemma extends A3 {
    function F(): bool
    ghost function G(): bool
    twostate function H(): bool

    method M()
    lemma N()  // error: lemma vs ghost method
    ghost method L()  // error: lemma vs ghost method
    twostate lemma K()

    least predicate P()
    greatest predicate Q()
    least lemma R()
    greatest lemma S()
  }

  class SwitchTwoState extends A3 {
    function F(): bool
    ghost function G(): bool
    twostate function H(): bool

    method M()
    twostate lemma N()  // error: lemma vs twostate
    twostate lemma L()  // error: lemma vs twostate
    lemma K()  // error: lemma vs twostate

    least predicate P()
    greatest predicate Q()
    least lemma R()
    greatest lemma S()
  }

  class SwitchExtreme0 extends A3 {
    function F(): bool
    ghost function G(): bool
    twostate function H(): bool

    method M()
    ghost method N()
    lemma L()
    twostate lemma K()

    greatest predicate P()  // error: least vs greatest
    least predicate Q()  // error: least vs greatest
    greatest lemma R()  // error: least vs greatest
    least lemma S()  // error: least vs greatest
  }

  class SwitchExtreme1 extends A3 {
    function F(): bool
    ghost function G(): bool
    twostate function H(): bool

    method M()
    ghost method N()
    least lemma L()  // error: extreme lemma vs lemma
    twostate lemma K()

    ghost predicate P()  // error: extreme predicate vs predicate
    ghost predicate Q()  // error: extreme predicate vs predicate
    lemma R()  // error: extreme lemma vs lemma
    lemma S()  // error: extreme lemma vs lemma
  }
}

module PredicateFunctionBool {
  trait A4 {
    ghost function F(): bool
    twostate function G(): bool

    ghost predicate M()
    twostate predicate N()
  }
  trait AAA extends A4 {
  }
  class C extends AAA {
    ghost predicate F() { true }
    twostate predicate G() { true }

    ghost function M(): bool { true }
    twostate function N(): bool { true }
  }
}
module ExtremeKMismatch {
  trait A4 {
    least predicate P()
    least predicate Q[nat]()
    least predicate R[ORDINAL]()

    least lemma K()
    least lemma L[nat]()
    least lemma M[ORDINAL]()
  }
  trait AAA extends A4 {
  }
  class C0 extends AAA {
    least predicate P()
    least predicate Q()  // error: nat vs ORDINAL
    least predicate R()

    least lemma K()
    least lemma L()  // error: nat vs ORDINAL
    least lemma M()
  }
  class C1 extends AAA {
    least predicate P[nat]()  // error: nat vs ORDINAL
    least predicate Q[nat]()
    least predicate R[nat]()  // error: nat vs ORDINAL

    least lemma K[nat]()  // error: nat vs ORDINAL
    least lemma L[nat]()
    least lemma M[nat]()  // error: nat vs ORDINAL
  }
  class C2 extends AAA {
    least predicate P[ORDINAL]()
    least predicate Q[ORDINAL]()  // error: nat vs ORDINAL
    least predicate R[ORDINAL]()

    least lemma K[ORDINAL]()
    least lemma L[ORDINAL]()  // error: nat vs ORDINAL
    least lemma M[ORDINAL]()
  }
}
