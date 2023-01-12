// RUN: %exits-with 2 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method BadParens0(xs: List)
{
  match xs
  case (Nil) => // error: parentheses are not allowed around a pattern
  case (Cons(h, t)) => // error: parentheses are not allowed around a pattern
}

method BadParens1(xs: List)
{
  match (xs)
  case (Nil) => // error: parentheses are not allowed around a pattern
  case (Cons(h, t)) => // error: parentheses are not allowed around a pattern
}

method Ghost1Tuple(xs: List)
{
  // These parentheses in patterns are fine, because they are the syntax of the constructor for a 1-tuple
  // with 1 ghost component.
  match (ghost xs)
  case (Nil) =>
  case (Cons(h, t)) =>
}
