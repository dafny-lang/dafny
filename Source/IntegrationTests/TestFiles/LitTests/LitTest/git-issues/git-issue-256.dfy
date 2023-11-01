// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


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

