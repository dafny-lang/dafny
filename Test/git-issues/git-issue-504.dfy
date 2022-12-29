// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module List {
  datatype t<A> = Nil | Cons(A, t<A>)
}

module Bug1 {
  import List

  function method foo(x: List.t<char>, y: List.t<char>): List.t<char> {
    match (x, y)
      case (Cons(_, _), _) => List.Cons('-', List.Nil)
      case (Nil, _) => List.Nil
  }
}

