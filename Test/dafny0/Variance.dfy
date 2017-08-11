// RUN: %dafny /print:"%t.print" /dprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype MyData<+A, =B, -C, D> =
  | MakeA(A)
  | MakeB(B)
  | MakeC(C)  // error: C is used in positive position
  | makeD(D)

type Syn<X, -Y, Z> = MyData<X, Y, Z, Z>
type Cyn<M, -N> = MyData<int -> M, M, N -> int, N>

class MyClass<=Inv> {
}

datatype CheckIt<+A> =
  | Cons(A, MyData<int,int,int,int>)
  | Fn(int ~> A)
  | Nf(A ~> int)  // error: A is used in negative position
  | Double((A ~> int) ~> int)
  | ToSet(real -> set<A>)
  | FromSet(set<A> ~> real)  // error: A is used in negative position
  | Classy(MyClass<A>)  // error: + passed in as =
  | MakeA(MyData<A,int,int,int>)
  | MakeB(MyData<int,A,int,int>)  // error: + passed in as =
  | MakeC(MyData<int,int,A,int>)  // error: + passed in as -
  | MakeD(MyData<int,int,int,A>)  // error: + passed in as =

class VaryingClass<A,B,C,+HotDog,D,-Whale>  // error (x2): all must be =
{
}

iterator VaryingIter<A,B,C,+HotDog,D,-Whale>()  // error (x2): all must be =
{
}
