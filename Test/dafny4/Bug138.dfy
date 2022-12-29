// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List = Nil | Cons(int, List)

method R(xs: List)
{
  match xs
  case Nil() =>    // currently produces a parsing error, but shouldn't
  case Cons(x, Nil()) =>  // currently allowed
  case Cons(x, Cons(y, tail)) =>
}

function F(xs: List) : int
{
  match xs
  case Nil() =>  0  // currently produces a parsing error, but shouldn't
  case Cons(x, Nil()) => 1 // currently allowed
  case Cons(x, Cons(y, tail)) => 2
}


