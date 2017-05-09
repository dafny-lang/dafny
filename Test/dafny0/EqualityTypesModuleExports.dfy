// RUN: %dafny /rprint:"%t.rprint" "%s" > "%t"
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
    function method Fib<X>(n: int, xs: set<X>): int  // this should infer X to be (==)
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
