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

// ----------------------------

module Gh {
  datatype D = Nil | Cons(head: int, tail: D, ghost x: int)

  method M(n: nat, b: bool, d: D, e: D, ghost g: bool)
    ensures b ==> d == e;  // fine, this is a ghost declaration
  {
    ghost var g := 0;
    var h := 0;
    if d == e {  // fine, this is a ghost statement
      g := g + 1;
    } else {
      assert !b;
    }
    if d == e {  // error: not allowed to compare D's in a non-ghost context
      h := h + 1;
    }
    if n != 0 {
      M(n-1, b, d, e, d==e);  // fine
      M(n-1, d==e, d, e, false);  // error, cannot pass in d==e like we do
    }
    GM(d==e, d, e);  // fine -- we're calling a ghost method
    var y0 := F(b, d==e);
    var y1 := F(d==e, false);  // error
  }

  function method F(b: bool, ghost g: bool): int { 6 }

  ghost method GM(b: bool, d: D, e: D)  // all equalities are fine in a ghost method
    ensures b ==> d == e;
  {
    ghost var g := 0;
    var h := 0;
    if d == e {
      g := g + 1;
    } else {
      assert !b;
    }
    if d == e {
      h := h + 1;
    }
  }
}
