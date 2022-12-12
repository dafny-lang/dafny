// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
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

  class Cl<Y(0)> extends Tr<(Y,Y)> {
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

  trait X0 extends C<(real, int)> { }
  trait X1<U> extends X0 { }
  trait X2<U> extends C<seq<U>> { }
  trait X3<U, V> extends C<(U, V)> { }
  trait X4<U> extends X3<U, int> { }
  trait X5<U> extends X3<real, U> { }
  trait X6 extends X4<real>, X0, X5<int> { }  // all of these work out to extend C<(real, int)>
  trait X7 extends X2<bool> { }
  trait X8 extends X6, X7, X1<array<bv19>> { }  // error: extends C<(real, int)> and C<seq<bool>> (just 1 error message)
  trait X9 extends X7, X6, X1<array<bv19>> { }  // error: extends C<(real, int)> and C<seq<bool>> (just 1 error message)
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
    static least predicate P()
    static greatest predicate Q()
    static least lemma IL()
    static greatest lemma CL()
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

    function method cif0(): int
    function gif0(): int
    function method cif1(): int
    function gif1(): int
    function method cif2(): int { 5 }
    function gif2(): int { 5 }
    function method cif3(): int { 5 }
    function gif3(): int { 5 }

    static function method csf0(): int
    static function gsf0(): int
    static function method csf1(): int
    static function gsf1(): int
    static function method csf2(): int { 2 }
    static function gsf2(): int { 2 }
    static function method csf3(): int { 2 }
    static function gsf3(): int { 2 }

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

  class Cl extends Tr {
    var civ: object  // error: cannot redeclare
    ghost var giv: object  // error: cannot redeclare
    const cic: object  // error: cannot redeclare
    ghost const gic: object  // error: cannot redeclare
    static const csc: object  // error: cannot redeclare
    ghost static const gsc: object  // error: cannot redeclare

    function method cif0(): int
    function gif0(): int
    function method cif1(): int { 5 }
    function gif1(): int { 5 }
    function method cif2(): int  // error: cannot redeclare member that already has a body
    function gif2(): int  // error: cannot redeclare member that already has a body
    function method cif3(): int { 5 }  // error: cannot redeclare member that already has a body
    function gif3(): int { 5 }  // error: cannot redeclare member that already has a body

    static function method csf0(): int  // error: cannot redeclare static member
    static function gsf0(): int  // error: cannot redeclare static member
    static function method csf1(): int { 2 }  // error: cannot redeclare static member
    static function gsf1(): int { 2 }  // error: cannot redeclare static member
    static function method csf2(): int  // error: cannot redeclare static member
    static function gsf2(): int  // error: cannot redeclare static member
    static function method csf3(): int { 2 }  // error: cannot redeclare static member
    static function gsf3(): int { 2 }  // error: cannot redeclare static member

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
    function method F(): bool
    function G(): bool
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

  class SwitchGhostStatus extends AAA {
    function F(): bool  // error: ghost mismatch
    function method G(): bool  // error: ghost mismatch
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

  class SwitchLemma extends AAA {
    function method F(): bool
    function G(): bool
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

  class SwitchTwoState extends AAA {
    function method F(): bool
    function G(): bool
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

  class SwitchExtreme0 extends AAA {
    function method F(): bool
    function G(): bool
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

  class SwitchExtreme1 extends AAA {
    function method F(): bool
    function G(): bool
    twostate function H(): bool

    method M()
    ghost method N()
    least lemma L()  // error: extreme lemma vs lemma
    twostate lemma K()

    predicate P()  // error: extreme predicate vs predicate
    predicate Q()  // error: extreme predicate vs predicate
    lemma R()  // error: extreme lemma vs lemma
    lemma S()  // error: extreme lemma vs lemma
  }
}

module PredicateFunctionBool {
  trait AAA {
    function F(): bool
    twostate function G(): bool

    predicate M()
    twostate predicate N()
  }
  class C extends AAA {
    predicate F() { true }
    twostate predicate G() { true }

    function M(): bool { true }
    twostate function N(): bool { true }
  }
}

module ExtremeKMismatch {
  trait AAA {
    least predicate P()
    least predicate Q[nat]()
    least predicate R[ORDINAL]()

    least lemma K()
    least lemma L[nat]()
    least lemma M[ORDINAL]()
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

// The tests in ProvidingModule and ImporterOfProvidingModule contain two
// regression tests, namely type parameters of the imported types and the
// duplicate generation of type tags for imported datatypes, which during
// one part of development were done incorrectly.
module ProvidingModule {
  export
    provides Trait, Trait.M, Trait.N
    provides Klass, Klass.M, Klass.N
    provides Dt, Dt.M, Dt.N

  trait Trait<AA> {
    const M := 100
    ghost const N: AA
  }
  class Klass<BB> {
    constructor () { }
    const M := 100
    ghost const N: BB
  }
  datatype Dt<CC(00)> = X | Y | More(u: int) {
    const M := 100
    ghost const N: CC
  }
}

module ImporterOfProvidingModule {
  import G = ProvidingModule

  method UsesField(t: G.Trait<int>, k: G.Klass<int>, d: G.Dt<int>) {
    var s := t.M + k.M + d.M;
    ghost var a := t.N;
    ghost var b := k.N;
    ghost var c := d.N;
  }
}

module NeedForConstructors {
  trait Tr<X> {
    var w: X
  }

  class AAA<Y> extends Tr<(Y,Y)> {  // error: AAA must declare a constructor, since w has type (Y,Y)
  }

  codatatype Forever'<G> = More(Forever'<int>)
  type Forever = Forever'<bool>
  class BBB extends Tr<Forever> {  // error: BBB must declare a constructor, since w has type Forever
  }

  class CCC<Y(0)> extends Tr<(Y,Y)> {
  }
}

module TypeCharacteristicsDiscrepancies {
  trait RequiresZero<X(0)> {
    var x: X
  }

  class ClassRequiresZero<Y(0)> {
  }

  codatatype Forever'<G> = More(Forever'<int>)
  type Forever = Forever'<bool>
  function method AlwaysMore(): Forever'<int> {
    More(AlwaysMore())
  }

  method M0() {
    var c0 := new ClassRequiresZero<int>;
    var c1 := new ClassRequiresZero<Forever>;  // error: cannot instantiate Y(0) with Forever
  }

  method M1(c0: ClassRequiresZero<int>, c1: ClassRequiresZero<Forever>) {  // error: cannot instantiate Y(0) with Forever
  }

  class HasZero0 extends RequiresZero<int> { }
  class HasZero1<Y(0)> extends RequiresZero<Y> { }
  class HasZero2<Y(0)> extends RequiresZero<(Y,Y)> { }
  class NoZero0 extends RequiresZero<Forever> {  // error: cannot instantiate X(0) with Forever
    constructor () {
      x := More(AlwaysMore());
    }
  }
  class NoZero1<Y> extends RequiresZero<Y> {  // error: cannot instantiate X(0) with Y
    constructor (y: Y) {
      x := y;
    }
  }
  class NoZero2<Y> extends RequiresZero<(Y,Y)> {  // error: cannot instantiate X(0) with (Y,Y)
    constructor (y: Y) {
      x := (y, y);
    }
  }

  class ClassWithFields<X> {
    var s: set<X>  // error: argument to set is required to support equality
  }

  trait AnythingGoes<X> {
  }

  class InnerError0 extends AnythingGoes<set<Forever>> { }  // error: set parameter must support (==)
  class InnerError1 extends AnythingGoes<RequiresZero<Forever>> { }  // error: RequiresZero parameter must support (0)
  class InnerError2 extends AnythingGoes<RequiresZero?<Forever>> { }  // error: RequiresZero? parameter must support (0)
}

module ExtendObject {
  trait A extends object { }
  trait B extends object? { }   // error: should say, object, not object?
  class C extends object { }
  class D extends object? { }   // error: should say, object, not object?
}

module TypeCharacteristics {
  trait Tr {
    method M<A, B(0), C(00), d(!new), E(==)>()
    function F<A, B(0), C(00), d(!new), E(==)>(): int
  }
  class C0 extends Tr {
    method M<R, S, T, U, V>()  // error (4x): type-characteristic mismatches
    function F<R, S, T, U, V>(): int  // error (4x): type-characteristic mismatches
  }
  class C1 extends Tr {
    method M<R(0), S(0), T(0), U(!new), V(==)>()  // error (2x): type-characteristic mismatches
    function F<R(0), S(0), T(0), U(!new), V(==)>(): int  // error (2x): type-characteristic mismatches
  }
  class C2 extends Tr {
    method M<R(00), S(00), T(00), U(!new), V(==)>()  // error (2x): type-characteristic mismatches
    function F<R(00), S(00), T(00), U(!new), V(==)>(): int  // error (2x): type-characteristic mismatches
  }
}
