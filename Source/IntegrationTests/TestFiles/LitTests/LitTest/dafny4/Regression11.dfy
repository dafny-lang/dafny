// RUN: %exits-with 2 %dafny /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Once upon a time, several of these would crash the resolver after it had reported
// that an error about an unresolved type name.

class MyClass<O> { }

ghost function F<Y>(x: int, Y: Y): int { x }


type Subset0<A> = x: int | var s: seq<A> := []; |s| == 0

type Subset1<A> = x: int | var s: seq<B> := []; |s| == 0  // error: B does not exist

newtype MyInt = x: int | var s: seq<C> := []; |s| == 0  // error: C does not exist

newtype MyO = x: int | var cl: MyClass<D> := null; cl == cl  // error: D does not exist

newtype MyQ = x: int | var cl: MaiKlass<object> := null; cl == cl  // error: MaiKlass does not exist


type Subset2<A> = x: int | exists a: A :: F(10, a) < 100

type Subset3<A> = x: int | forall b: B :: F(20, b) < 100  // error: B does not exist

newtype MyInt' = x: int | forall c: C :: F(30, c) < 100  // error: C does not exist

newtype MyO' = x: int | var cl: MyClass<int,D> := null; cl == cl  // error: D does not exist
