// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<S> = Nil | Cons(car: S, cdr: List<S>)

function {:simp} simp<X>(x: X): X { x }

function method {:opaque} Length<U>(xs: List<U>): nat
{
  match xs
    case Nil => 0
    case Cons(x, xs') => 1 + Length(xs')
}

lemma {:simp} Length_simp<T>(x: T, xs: List<T>)
  ensures Length<T>(Cons(x, xs)) == 1 + Length<T>(xs)
{
  reveal Length();
}

lemma {:simp} Length_Nil<T>()
  ensures Length<T>(Nil) == 0
{
  reveal Length();
}

function Length2<T>(x: T, y: T): nat
{
  simp(Length(Cons(x, Cons(y, Nil))))
}

lemma Length2_2<T>(x: T, y: T)
  ensures Length2(x, y) == 2
{
}
