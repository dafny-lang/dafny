// RUN: %exits-with 2 %dafny /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This module contains checks that (==) types are inferred and required as they should.
module AAA {
  iterator IterA<Xyz>(u: set<Xyz>)  // this should infer Xyz to be (==)

  iterator IterB<Qpr>()
    requires var s: set<Qpr> := {}; |s| == 0  // fine, since Qpr is used only in the specification

  iterator IterC<Klm>()
  {
    var u: set<Klm> := {};  // error (x2): decl. of "u" and "{}" would require Klm to be declared with (==)
  }

  iterator IterD<Klm(==)>()
  {
    var u: set<Klm> := {};  // good now
  }

  class MyClass<GG,HH(==)> {
    function Fib<X>(n: int, xs: set<X>): int  // this should infer X to be (==)
    {
      if n < 2 then n else Fib(n-2, xs) + Fib(n-1, xs)
    }
    method Mrris<Y,Z>(b: bool, y: Y) returns (zz: set<Z>)  // this should infer Z to be (==)
    {
      if b {
        zz := Mrris(false, y);
      }
      var v := Fib(10, zz);
      var k := Fib(10, {y});  // error (x2): type parameter to Fib requires (==), but Y is not declared as such
    }
    method P(g: set<GG>)  // error: this requires GG to be (==)
    method Q(h: set<HH>)
  }

  trait Trait {
  }

  // The following types all take (==) arguments
  datatype Dt0<X> = Make0(d: Dt1)
  datatype Dt1<Y> = Make1(d: Dt2) | MakeAlt(s: multiset<Y>)
  datatype Dt2<Z> = Make2(d: Dt0)

  datatype ListWithALittlExtra<T> = Nil | Cons(head: T, tail: ListWithALittlExtra<T>, ghost extra: int)  // this is not a (==) type

  method TestDt<M,M'(==)>()
  {
    var a: Dt0<M>;  // error: Dt0 requires an (==) argument
    var b: Dt1<M>;  // error: Dt1 requires an (==) argument
    var c: Dt2<M>;  // error: Dt2 requires an (==) argument
    var a': Dt0<M'>;
    var b': Dt1<M'>;
    var c': Dt2<M'>;
  }

  // The first type parameter in each of the following requires a (==) type
  codatatype Co0<X,A> = Make0(d: Co1)
  codatatype Co1<Y,B> = Make1(d: Co2, e: set)
  codatatype Co2<Z,C> = Make2(d: Co0)

  method TestCo<M,A,M'(==)>()
  {
    var a: Co0<M,A>;  // error: Co0 requires an (==) for type argument 0
    var b: Co1<M,A>;  // error: Co1 requires an (==) for type argument 0
    var c: Co2<M,A>;  // error: Co2 requires an (==) for type argument 0
    var a': Co0<M',A>;
    var b': Co1<M',A>;
    var c': Co2<M',A>;
  }

  type Opaque0
  type Opaque1<A>
  type Opaque2<B(==),C>
  type O'Pake0(==)
  type O'Pake1(==)<A>
  type O'Pake2(==)<B,C(==)>

  type Syn0 = int
  type Syn1<A> = (int,A)  // this infers <A(==)>
  type Syn2<A(==)> = (int,A)
  type Syn3(==) = int
  type Syn4(==)<A> = (real,A)  // error: RHS is not (==) unless A is
  type Syn5(==)<A(==)> = (char,A)
  type Syn6<C,K> = Co0<C,K>  // this infers <C(==),K>

  type Subset0 = x | x < 100
  type Subset1<A> = s: set<A> | |s| == 0
  type Subset2<A(==)> = s: set<A> | |s| == 0
  type Subset3<A> = x: int | var s: seq<A> := []; |s| == 0  // fine, because seq<A> is used in a ghost context
  type Subset4(==)<A> = x: (A,int) | x.1 < 7  // error: RHS does not support equality, despite what is advertised

  method TestType<M,M'(==)>()
  {
    var a: Opaque0;
    var b: Opaque1<M>;
    var b': Opaque1<M'>;
    var c: Opaque2<M,M'>;  // error: type parameter 0 has to be (==)
    var c': Opaque2<M',M>;
    var d: O'Pake0;
    var e: O'Pake1<M>;
    var e': O'Pake1<M'>;
    var f: O'Pake2<M,M'>;
    var f': O'Pake2<M',M>;  // error: type parameter 1 has to be (==)

    var g: Syn0;
    var h: Syn1<M>;
    var h': Syn1<M'>;
    var i: Syn2<M>;  // error: type parameter has to be (==)
    var i': Syn2<M'>;
    var j: Syn3;
    var k: Syn4<M>;
    var k': Syn4<M'>;
    var l: Syn5<M>;  // error: type parameter has to be (==)
    var l': Syn5<M'>;
    var m: Syn6<M,M'>;  // error: type parameter 0 has to be (==)
    var m': Syn6<M',M>;

    var n: Subset0;
    var o: Subset1<M>;  // error: type parameter has to be (==)
    var o': Subset1<M'>;
    var p: Subset2<M>;  // error: type parameter has to be (==)
    var p': Subset2<M'>;
  }

  method TestTypesThemselves()
  {
    var a: Syn5<IterC<int>>;
    var b: Syn5<MyClass<int,int>>;
    var c: Syn5<Trait>;
    var d: Syn5<Dt0<int>>;
    var e: Syn5<ListWithALittlExtra<int>>;  // error: type argument to Syn5 is expected to be (==)
    var f: Syn5<Co2<int,int>>;  // error: type argument to Syn5 is expected to be (==)
    var g: Syn5<Opaque0>;  // error: type argument to Syn5 is expected to be (==)
    var h: Syn5<O'Pake0>;
    var i: Syn5<Syn5<int>>;
    var j: Syn5<Syn3>;
    var k: Syn5<Syn1<int -> int>>;  // error: type argument to Syn5 is expected to be (==)
    var l: Syn5<Subset3<Opaque0>>;
  }
}

module BBB {
  class MyClass<A(==)> { }
  datatype Dt<A> = Dt(s: set<A>)
  codatatype Co<A> = Co(s: iset<A>, more: SubsetCo<A>)
  type Syn<A> = Dt<A>
  type SubsetCo<A> = co: Co<A> | true  // error: Co and subset type SubsetCo have a mutual dependency
  type Noeq = int -> int

  method Test() {
    var a: MyClass<Noeq>;  // error: Noeq does not support equality
    var b: Dt<Noeq>;  // error: Noeq does not support equality
    var c: Co<Noeq>;  // error: Noeq does not support equality
    var d: Syn<Noeq>;  // error: Noeq does not support equality
    var e: SubsetCo<Noeq>;  // error: Noeq does not support equality
  }
}

module CCC {
  export reveals Co, Syn, SubsetCo, Dt
  export Alt reveals MyClass, Dt, SubsetCo, Co
  export More reveals Syn provides Dt

  class MyClass<A(==)> { }
  datatype Dt<A(==)> = Dt(s: set<A>)
  codatatype Co<A> = Co(s: iset<A>, more: SubsetCo<A>)
  type Syn<A> = Dt<A>
  type SubsetCo<A> = co: Co<A> | true  // error: Co and subset type SubsetCo have a mutual dependency
  type Noeq = int -> int

  method Test() {
    var a: MyClass<Noeq>;  // error: Noeq does not support equality
    var b: Dt<Noeq>;  // error: Noeq does not support equality
    var c: Co<Noeq>;  // error: Noeq does not support equality
    var d: Syn<Noeq>;  // error: Noeq does not support equality
    var e: SubsetCo<Noeq>;  // error: Noeq does not support equality
  }
}

module DDD {
  export reveals Syn, SubsetCo provides Dt, Co
  export Alt reveals MyClass, Dt, SubsetCo, Co
  export More reveals Syn, Dt

  class MyClass<A(==)> { }
  datatype Dt<A> = Dt(s: set<A>)  // error: A is not inferred to be (==), so set<A> is not allowed
  codatatype Co<A> = Co(s: iset<A>, more: SubsetCo<A>)  // error: A is not inferred to be (==), so iset<A> is not allowed
  type Syn<A> = Dt<A>
  type SubsetCo<A> = co: Co<A> | true  // error: Co and subset type SubsetCo have a mutual dependency
  type Noeq = int -> int

  method Test() {
    var a: MyClass<Noeq>;  // error: Noeq does not support equality
    // Nothing wrong with the following declarations, though, since the types are declared with, nor have been inferred to have, (==) arguments
    var b: Dt<Noeq>;
    var c: Co<Noeq>;
    var d: Syn<Noeq>;
    var e: SubsetCo<Noeq>;
  }
}

module EEE {
  type Opa(==)<A>
  type Syn(==)<A> = int
  type Sub(==)<A> = x: bool | !x
  type Opa'<A>
  type Syn'<A> = int
  type Sub'<A> = x: bool | !x
}
module FFF refines EEE {
  type Noeq = int -> int
  type Opa<A> = Noeq  // error: Opa must support equality
}
module GGG refines EEE {
  export provides Opa, Syn, Sub, Opa', Syn', Sub'
}
module HHH {
  import GGG
  type Noeq = int -> int
  type S<A> = set<A>
  method Test() {
    var a: GGG.Opa<Noeq>;
    var b: GGG.Syn<Noeq>;
    var c: GGG.Sub<Noeq>;
    var d: S<GGG.Opa<int>>;
    var e: S<GGG.Syn<int>>;
    var f: S<GGG.Sub<int>>;
    var d': S<GGG.Opa'<int>>;  // error: type parameter to S must support equality, but it doesn't
    var e': S<GGG.Syn'<int>>;  // error: type parameter to S must support equality, but it doesn't
    var f': S<GGG.Sub'<int>>;  // error: type parameter to S must support equality, but it doesn't
  }
}

module WWW0 {
  export provides XT, YT, ZT, WT, YT', ZT', WT'
  datatype XT = Blue | Red
  type YT = XT
  type ZT
  type WT = x: int | x < 100
  type YT'(==) = XT
  type ZT'(==)
  type WT'(==) = x: int | x < 100
}
module WWW1 {
  import WWW0
  method M(x: WWW0.XT, y: WWW0.YT, z: WWW0.ZT, w: WWW0.WT) returns (r: int) {
    if x == x {  // error: x's type is not known to support equality
      r := 20;
    }
    if y == y {  // error: y's type is not known to support equality
      r := 20;
    }
    if z == z {  // error: z's type is not known to support equality
      r := 20;
    }
    if w == w {  // error: w's type is not known to support equality
      r := 20;
    }
  }
  method M'(y: WWW0.YT', z: WWW0.ZT', w: WWW0.WT') returns (r: int) {
    if y == y {
      r := 20;
    }
    if z == z {
      r := 20;
    }
    if w == w {
      r := 20;
    }
  }
}

module QQQ0 {
  type Syn<A> = int
}
module QQQ1 refines QQQ0 {
  export provides Syn
}
module PPP {
  import QQQ1
  type A(==) = QQQ1.Syn<int>  // error: QQQ.Syn1 is not known to support equality
}

module PRS {
  export provides S  // exports will not know S to be equality-supporting, but this is known locally
  datatype Dt = Green | Cat
  type S = Dt
  method M(s: S, t: S) returns (b: bool) {
    b := s == t;
  }
}

module ExportEquality0 {
  export provides ExportedType, Empty

  type ExportedType(==)<A> = PrivateType<A>  // error: because PrivateType<A> supports equality only if A does
  datatype PrivateType<A> = None | Make(a: A)
  function Empty(): ExportedType
}

module ExportEquality1 {
  export provides ExportedType, Empty

  type ExportedType(==)<A> = PrivateType<A>
  datatype PrivateType<A> = None | Make(a: int)  // this does not make use of A
  function Empty(): ExportedType
}

module ExportEquality2 {
  export provides ExportedType, Empty

  type ExportedType(==)<A(==)> = PrivateType<A>
  datatype PrivateType<A> = None | Make(a: A)
  function Empty(): ExportedType
}
module Client2 {
  import EE = ExportEquality2
  method IsEmpty(t: EE.ExportedType) returns (wellIsIt: bool)
  {
    wellIsIt := t == EE.Empty();
  }
}

module ExportEquality3 {
  export provides ExportedType, Empty, IsEmpty

  type ExportedType(==)<A(==)> = PrivateType<A>
  datatype PrivateType<A> = None | Make(a: A)
  function Empty(): ExportedType
  {
    None
  }
  predicate IsEmpty(t: ExportedType)
    ensures IsEmpty(t) <==> t == Empty()
  {
    t == None
  }
}

module CompareWithNullaryCtor {
  datatype List<A> = Nil | Cons(head: A, tail: List)
  predicate MyEquals_Bad<A>(xs: List, ys: List)
  {
    xs == ys  // error: List<A> supports equality only if A does
  }
  predicate MyEquals_Good<A(==)>(xs: List, ys: List)
  {
    xs == ys
  }
  predicate IsNil<A>(xs: List)
  {
    xs == Nil
  }
  predicate IsNil'<A>(xs: List)
  {
    xs.Nil?
  }
}

module ProbablyAMistake {
  // The following line is legal syntactically, but it's suspicious, because there's
  // already a member called "F" in the module and this export set is empty; hence, to
  // try to be helpful, a warning is produced.
  export F  // warning: a possible mix-up of "export" syntax
  ghost function F(x: int): int { x }
}

module AHarmlessMistake {
  // The following line may also be a mistake, but since empty export sets are allowed
  // and there's no member named "G", there's no strong evidence to suggest producing
  // a possibly spurious warning.
  export G
  ghost function F(x: int): int { x }
}

// -----------------------------------------------
// Some regression tests for scoping

module ScopeRegressions {
  module A {
    import B

    type AType = b: B.BType |
      P(b) ghost witness var h: B.BType :| true; h

    ghost predicate P(b: B.BType) { true }

    method M(a: AType) returns (b: B.BType)
    {
      // The following assignment once didn't use to type check properly
      b := a;
    }
  }
  module B {
    // To the outside world, "BType" is just an opaque type
    export provides BType
    datatype BType = X | Y
  }
}

// ------------------------------------------------------
// Tests that all declared type characteristics hold true
// ------------------------------------------------------

module SynonymTypes {
  type Empty = x: int | false witness *
  type Synonym(0) = Empty  // error
  type AnotherSynonym(00) = Empty  // error

  type NonEmpty = x: int | 0 <= x ghost witness 2
  type NESynonym(0) = NonEmpty  // error
  type NEAnotherSynonym(00) = NonEmpty

  class C { }
  type NoReference(!new) = C?  // error

  codatatype Stream = More(Stream)
  type PipeDreamEquality(==) = Stream  // error
}

module SubsetTypes {
  type Empty = x: int | false witness *
  type Subset(0) = e: Empty| true  // error
  type AnotherSubset(00) = e: Empty | true  // error

  type NonEmpty = x: int | 0 <= x ghost witness 2
  type NESynonym(0) = e: NonEmpty | true  // error
  type NEAnotherSynonym(00) = e: NonEmpty | true

  class C { }
  type NoReference(!new) = c: C? | true  // error

  codatatype Stream = More(Stream)
  type PipeDreamEquality(==) = s: Stream | true  // error
}
