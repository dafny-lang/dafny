// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

datatype List<T> = Nil | Cons(T, List<T>) {
  function App(ys: List<T>): List<T> {
    match this
      case Nil => ys
      case Cons(x, xs) => Cons(x, xs.App(ys))
  }

  static ghost function Concat<T>(l: List<List<T>>): List<T> {
    match l
      case Nil => Nil
      case Cons(x, xs) => x.App(Concat(xs))
  }

  lemma AppAssoc(m: List<T>, n: List<T>)
    ensures App(m).App(n) == App(m.App(n))
  {}

  static lemma ConcatApp<T>(l1: List<List<T>>, l2: List<List<T>>)
    ensures Concat(l1.App(l2)) == Concat(l1).App(Concat(l2))
  {
      match l1
        case Nil =>
        case Cons(x, xs) =>
          x.AppAssoc(Concat(xs), Concat(l2));
  }
}

method Main() {}
