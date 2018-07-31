// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simp} simp<T>(x: T): T
{
  x
}

datatype List<T> = Nil | Cons(car: T, cdr: List<T>)

function Length<T>(xs: List<T>): nat
{
  match xs
    case Nil => 0
    case Cons(x, xs') => 1 + Length(xs')
}

lemma {:simp} Cons_simp(x: int, xs: List<int>)
  ensures Length(Cons(x, xs)) == 1 + Length(xs)
{
}

lemma {:simp} Cons_Nil()
  ensures Length<int>(Nil) == 0
{
}

function len2(x: int, y: int): nat
{
  simp(Length(Cons(x, Cons(y, Nil))))
}

lemma len2_2(x: int, y: int)
  ensures len2(x, y) == 2
{
}
