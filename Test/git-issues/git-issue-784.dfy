// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(T, List<T>) {
  function method App(ys: List<T>): List<T> {
    match this
      case Nil => ys
      case Cons(x, xs) => Cons(x, xs.App(ys))
  }

  static function method Concat<T>(l: List<List<T>>): List<T> {
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
