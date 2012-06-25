module A {
  datatype Explicit<T(==)> = Nil | Cons(set<T>, Explicit<T>);
  datatype Inferred<T> = Nil | Cons(set<T>, Inferred<T>);

  class C {
    method M<T>(x: Explicit<T>)
    method N<T>(x: Inferred<T>)
  }
}

module B refines A {
  class C {
    method M<T>(x: Explicit<T>)
    method N<T(==)>(x: Inferred<T>)
  }
}

// ----------------------------

module C {
  type X(==);
  type Y(==);
}

module D refines C {
  class X { }
  datatype Y = Red | Green | Blue;
}

module E refines C {
  codatatype X = Next(int, X);  // error: X requires equality and codatatypes don't got it
  datatype Y = Nil | Something(Z) | More(Y, Y);  // error: Y does not support equality
  codatatype Z = Red | Green(X) | Blue;
}

module F refines C {
  datatype X<T> = Nil | Cons(T, X<T>);  // error: not allowed to add a type parameter to type X
  class Y<T> { }  // error: not allowed to add a type parameter to type Y
}

module G refines C {
  datatype X = Nil | Next(Z, X);  // error: X does not support equality
  datatype Y = Nil | Something(Z) | More(Y, Y);  // error: Y does not support equality
  codatatype Z = Red | Green | Blue;
}

// ----------------------------

module H {
  datatype Dt<T> = Nil | Cons(T, Dt);

  datatype BulkyList<T> = Nothing | Wrapper(T, BulkyListAux);
  datatype BulkyListAux<T> = Kons(set<T>, BulkyListAuxAux);
  datatype BulkyListAuxAux<T> = GoBack(BulkyList);

  codatatype Stream<T> = Next(head: T, tail: Stream<T>);

  method M<T(==)>(x: T)
  { }
  function method F<T>(x: BulkyList<T>, y: BulkyList<T>): int
  { if x == y then 5 else 7 }  // this equality is allowed
  function method G<T>(x: Dt<T>, y: Dt<T>): int
  { if x == y then 5 else 7 }  // error: the equality is not allowed, because Dt<T> may not support equality
  function method G'<T(==)>(x: Dt<T>, y: Dt<T>): int
  { if x == y then 5 else 7 }  // fine

  method Caller0(b: BulkyList, y: int) {
    match (b) {
      case Nothing =>
      case Wrapper(t, bla) =>
        var u;
        if (y < 100) { u := t; }
        // The following call is allowed, because it will be inferred that
        // 'u' is of a type that supports equality
        M(u);
    }
  }
  method Caller1(d: Dt) {
    match (d) {
      case Nil =>
      case Cons(t, rest) =>
        M(t);  // error: t may be of a type that does not support equality
    }
  }
  method Caller2(co: Stream) {
    var d := Cons(co, Nil);
     Caller1(d);  // case in point for the error in Caller1
  }
}
