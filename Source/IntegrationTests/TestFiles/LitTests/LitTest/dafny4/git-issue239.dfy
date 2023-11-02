// RUN: %testDafnyForEachResolver "%s"


module List {
  datatype list<A> = Nil | Cons(A, list<A>)

  function split<A, B>(l: list<(A, B)>): (list<A>, list<B>) {
    match l
      case Nil =>  (Nil, Nil)
      case Cons((x, y), xys) =>
        var (xs, ys) := split(xys);
        (Cons(x, xs), Cons(y, ys))
  }
}
