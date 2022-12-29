// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module List {
  datatype t<A> = Nil | Cons(A, t<A>)
}

module String_Utils {
  import List
  lemma compareNth(A : List.t<char>, B : List.t<char>) {
     match (A, B)
      case (Nil, Cons(_, _)) =>
  }
  lemma compare(A : List.t<char>, B : List.t<char>) {
     match (A, B)
      case (Nil, Cons(_, _)) =>
      case (Nil, Nil) =>
      case (Cons(_, _), _) =>
  }
}

