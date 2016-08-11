// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type MyType<A> = int

type Int = int

type PairaBools = (bool, bool)

datatype List<T> = Nil | Cons(T, List)

type Synonym0<T,U> = List<T>

type Synonym1<T> = List  // type argument of List filled in automatically

type Synonym2<A> = List<A>

type Synonym3<B> = Synonym4

type Synonym4<C> = Synonym2<C>

type Synonym5<A,B> = List

function Plus(x: Int, y: int): Int
{
  x + y
}

method Next(s: Synonym1) returns (u: Synonym1)
{
  match s
  case Nil => u := Nil;
  case Cons(_, tail) => u := tail;
}

method Add<W>(t: W, s: Synonym1) returns (u: Synonym1)
{
  u := Cons(t, Nil);
}

function Skip(s: Synonym3): Synonym0
{
  match s
  case Nil => Nil
  case Cons(_, tail) => tail
}

type MyMap = map<int, map<real, bool>>

predicate MyMapProperty(m: MyMap, x: int)
{
  x in m && x as real in m[x] && m[x][x as real]
}
