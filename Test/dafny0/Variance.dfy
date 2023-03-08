// RUN: %exits-with 2 %dafny /print:"%t.print" /dprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module VarianceChecks {
  datatype MyData<+A, *B, !C, D, -E> =
    | MakeA(A)
    | MakeB(B)
    | MakeC(C)
    | MakeD(D)
    | MakeE(E)  // error: E is used in positive position

  type Syn<X, -Y, Z> = MyData<X, Y, Z, Z, Z>  // error (x3)
  type Cyn<M, -N> = MyData<int -> M, M, N -> int, N, N -> int>  // error (x4)

  class MyClass<!Inv> {
  }

  datatype CheckIt<+A, *B, !C, D, -E> =
    | Cons(A, MyData<int,int,int,int,int>)
    | Fn(int ~> A)
    | Nf(A ~> int)  // error: A is used in negative position
    | Double((A ~> int) ~> int)  // error: A is not in a strict positive position
    | ToSet(real -> set<A>)
    | FromSet(set<A> ~> real)  // error: A is used in negative position
    | Classy(MyClass<A>)  // error: + passed in as =
    | MakeA(MyData<A,int,int,int,int>)
    | MakeB(MyData<int,A,int,int,int>)  // error: + passed in as *
    | MakeC(MyData<int,int,A,int,int>)  // error: + passed in as !
    | MakeD(MyData<int,int,int,A,int>)  // error: + passed in as (default)
    | MakeE(MyData<int,int,int,int,A>)  // error: + passed in as -
    | CreateA(MyData<B,int,int,int,int>)
    | CreateB(MyData<int,B,int,int,int>)
    | CreateC(MyData<int,int,B,int,int>)  // error: * passed in as !
    | CreateD(MyData<int,int,int,B,int>)  // error: * passed in as (default)
    | CreateE(MyData<int,int,int,int,B>)  // error: * passed in as -
    | DoA(MyData<C,int,int,int,int>)
    | DoB(MyData<int,C,int,int,int>)
    | DoC(MyData<int,int,C,int,int>)
    | DoD(MyData<int,int,int,C,int>)
    | DoE(MyData<int,int,int,int,C>)
    | FabricateA(MyData<D,int,int,int,int>)
    | FabricateB(MyData<int,D,int,int,int>)  // error: strict passed to context without strict restrictions
    | FabricateC(MyData<int,int,D,int,int>)  // error: strict passed to context without strict restrictions
    | FabricateD(MyData<int,int,int,D,int>)
    | FabricateE(MyData<int,int,int,int,D>)  // error: strict passed to negative context
    | BorrowA(MyData<E,int,int,int,int>)  // error: - passed in as +
    | BorrowB(MyData<int,E,int,int,int>)  // error: - passed in as *
    | BorrowC(MyData<int,int,E,int,int>)  // error: - passed in as !
    | BorrowD(MyData<int,int,int,E,int>)  // error: - passed in as (default)
    | BorrowE(MyData<int,int,int,int,E>)
    | ISetA(iset<A>)  // error: - strict passed to context without strict restrictions
    | ISetB(iset<B>)
    | ISetC(iset<C>)
    | ISetD(iset<D>)  // error: - strict passed to negative context
    | ISetE(iset<E>)  // error: - contravariant passed to covariant context
    | SetA(set<A>)
    | SetB(set<B>)
    | SetC(set<C>)
    | SetD(set<D>)
    | SetE(set<E>)  // error: - contravariant passed to covariant context
    | IMapAB(imap<A, B>)  // error: - strict passed to context without strict restrictions
    | IMapAE(imap<B, E>)  // error: - contravariant passed to covariant context
    | IMapBD(imap<B, D>)
    | IMapDB(imap<D, B>)  // error: - strict passed to context without strict restrictions

  type {:extern} abs<+A, *B, !C, D, -E>

  datatype CheckRec =
    | IMapD(imap<CheckRec, int>)  // error: - recursive mentions must be used in a strict (and covariant) context
    | IMapR(imap<int, CheckRec>)
    | ISet(iset<CheckRec>)  // error: - recursive mentions must be used in a strict (and covariant) context
    | Set(set<CheckRec>)
    | CheckA(abs<CheckRec, int, int, int, int>)
    | CheckB(abs<int, CheckRec, int, int, int>)  // error: - recursive mentions must be used in a strict (and covariant) context
    | CheckC(abs<int, int, CheckRec, int, int>)  // error: - recursive mentions must be used in a strict (and covariant) context
    | CheckD(abs<int, int, int, CheckRec, int>)
    | CheckE(abs<int, int, int, int, CheckRec>)  // error: - recursive mentions must be used in a strict (and covariant) context

  datatype CheckRec2 =
    | ArrowD(CheckRec2 -> int)  // error: - recursive mentions must be used in a strict (and covariant) context
    | ArrowR(int -> CheckRec2)

  class VaryingClass<A,B,C,+HotDog,D,-Whale>  // error (x2): all must be non-variant
  {
    var f: HotDog -> Whale  // not a problem here
    method M() {
      var g: HotDog -> Whale;  // not a problem here
    }
  }

  iterator VaryingIter<A,B,C,+HotDog,D,-Whale>()  // error (x2): all must be non-variant
  {
  }

  datatype Dt = Ctor(Dt -> int)  // error: this would give rise to a logical inconsistency

  datatype U0<!A> = U0(A -> bool)
  type U1<!A> = U0<A>
  datatype U2 = MakeU2(U1<U2>)  // error: this would give rise to a logical inconsistency

  datatype R0 = Ctor(R2 ~> bool)  // error: this would give rise to a logical inconsistency
  type R1<X> = X
  datatype R2 = Ctor(R1<R0>)
}

module Cycles {
  type W0 = W1
  datatype W1 = Ctor(W0 --> bool) // error: this increases cardinality

  datatype Z0 = Ctor(Z2 ~> bool) // error: this increases cardinality
  type Z1 = Z0
  datatype Z2 = Ctor(Z1)
}

module Depen {
  type V0 = x: V2 | true  // error: recursive definition in constraint of subset type
  type V1 = V0
  datatype V2 = Ctor(V1 --> bool)
}

module DependencyChecks {
  type A = x: B | true  // error: bad dependency cycle
  type B = y: int | F(y)
  ghost predicate F(y: int) {
    var i: A := 5;
    i < 32
  }

  datatype Q = Q(x: R)
  type R = x: S | true  // error: bad dependency cycle
  type S = y: int | G(y)
  ghost predicate G(y: int) {
    var q: Q :| true;
    q.x < 32
  }
}

module Cycle0 {
  type B = x: B | true  // error: cycle
}

module Cycle1 {
  type A = x: int | var a: A :| true; P(x)  // error: cycle
  ghost predicate P(x: int)
}

module Cycle2 {
  type C = x: int | f(x) == f(x)  // error: cycle
  ghost function f(x: int): C
}

module MoreDependencyCycles0 {
  type MeAndMyself = x: int | var m: MeAndMyself := 5; m < 10  // error: cyclic dependency in constraint
}

module MoreDependencyCycles1 {
  type MeAndMyself'' = MeAndMyself'
  type MeAndMyself' = x: int | var m: MeAndMyself'' := 5; m < 10  // error: cyclic dependency in constraint
}
