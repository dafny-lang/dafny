// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

/* Error: parentheses are not allowed around a pattern */
method AssertionFailure(xs: List)
{
  match xs
  case (Nil) =>
  case (Cons(h, t)) =>
}

