// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  datatype Explicit<T(==)> = Nil | Cons(set<T>, Explicit<T>)
  datatype Inferred<T> = Nil | Cons(set<T>, Inferred<T>)

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
  type X(==)
  type Y(==)
}

module D refines C {
  class X { }
  datatype Y = Red | Green | Blue
}

module E refines C {
  codatatype X = Next(int, X)  // error: X requires equality and codatatypes don't got it
  datatype Y = Nil | Something(Z) | More(Y, Y)  // error: Y does not support equality
  codatatype Z = Red | Green(X) | Blue
}

module F refines C {
  datatype X<T> = Nil | Cons(T, X<T>)  // error: not allowed to add a type parameter to type X
  class Y<T> { }  // error: not allowed to add a type parameter to type Y
}

module G refines C {
  datatype X = Nil | Next(Z, X)  // error: X does not support equality
  datatype Y = Nil | Something(Z) | More(Y, Y)  // error: Y does not support equality
  codatatype Z = Red | Green | Blue
}

// ----------------------------

module H {
  datatype Dt<T> = Nil | Cons(T, Dt)

  datatype BulkyList<T> = Nothing | Wrapper(T, BulkyListAux)
  datatype BulkyListAux<T> = Kons(set<T>, BulkyListAuxAux)
  datatype BulkyListAuxAux<T> = GoBack(BulkyList)

  codatatype Stream<T> = Next(head: T, tail: Stream<T>)

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

// ------ deeper nesting ------

module Deep {
  codatatype Co = Mo(Co) | NoMo
  class C<T> { }

  method M(a: set<C<Co>>) {
    var s: set<C<Co>>;
    var t: set<Co>;  // error: set element type must support equality
    var co: Co;
    var d := G(co, NoMo);  // error: actual type parameter for Y (namely, Co) does
                           // not support equality
    d := G(t, t) + G(s, s);  // fine, because all sets support equality
  }

  function method G<Y(==)>(y: Y, z: Y): int { if y == z then 5 else 7 }

  method P(b: set<Co>) {  // error: set element type must be a type with equality
  }

  ghost method Q(b: set<Co>) {  // fine, since this is a ghost method
  }

  method R(ghost b: set<Co>) {  // fine, since this is a ghost parameter
  }

  datatype Dt<T> = Bucket(T)
  datatype Left<T,U> = Bucket(T)
  datatype Right<T,U> = Bucket(set<U>)  // note, Dafny infers that U should be U(==)
  datatype RightExplicit<T,U(==)> = Bucket(set<U>)
  type Syn<A,B,C> = Left<C,A>

  method W<alpha(==)>()
  {
    var a: set<Dt<Co>>;  // error: Dt<Co> does not support equality
    var b: set<Dt<int>>;
    var c: set<Left<int,Co>>;
    var d: set<Left<Co,int>>;  // error: Left<Co,...> does not support equality
    var e: set<Right<Co,Co>>;  // error: type parameter 1 to Right is required to support equality
    ghost var e': set<Right<Co,Co>>;  // fine, since this is a ghost field
    var e'': set<RightExplicit<Co,Co>>;  // error: cannot instantiate argument 1 with Co
    var f: set<Syn<Co,Co,int>>;
    var g: set<Syn<int,int,Co>>;  // error: Syn<int,int,Co> does not support equality
    ghost var h: set<Syn<int,int,Co>>;  // in a ghost context, it's cool, though

    var i;  // error: inferred type (set<Co>) uses invalid set-element type
    var j: set;  // error: ditto
    ghost var k: set<Co>;  // type allowed here, because it's a ghost
    assert i == k || j == k || true;  // this infers the types of 'i' and 'j'
  }

  method StatementsWithVariables(a: set<C<Co>>) {
    var s: set<C<Co>>;
    var t: set<Co>;  // error: bad type
    ghost var u: set<Co>;

    var c := new ABC;
    forall x | x in {t} {  // error: bad type for x
      c.f := 0;
    }
    if t == u {
      forall x | x in {t}  // fine, because this is a ghost statement
        ensures true;
      {
      }
    }
  }

  class ABC { var f: int; }

  method Expressions() {
    var t: set<Co>;  // error: bad type
    var b := forall x | x in {t} :: x == x;  // error: bad type
    var y := var k: set<Co> := t; k <= t;  // error: bad type
  }

  ghost method GhostThings0(t: set<Co>) {
    assert forall x | x in {t} :: x == x;
    var y := var k: set<Co> := t; k <= t;
    assert y;
  }

  method GhostThings1(ghost t: set<Co>) {
    assert forall x | x in {t} :: x == x;
    ghost var y := var k: set<Co> := t; k <= t;
    assert y;
  }

  method InferEqualitySupportIsRequired<A>(s: set<A>)
  ghost method DontInferEqualitySupportIsRequired<A>(s: set<A>)
  method Explicit<A(==)>(s: set<A>)
  method TakesABoolean(b: bool)
  method AClient(co: Co, ko: Co) {
    Explicit({5});
    Explicit({co});  // error: bad type
    var b := ko in {co};  // error: bad type (argument for the set)
    ghost var bg := ko in {co};  // fine, it's a ghost
    InferEqualitySupportIsRequired({co});  // error: bad type
    DontInferEqualitySupportIsRequired({co});
    TakesABoolean(ko in {co});  // error: bad type
    var x := multiset([co,ko,co,ko])[ko];  // error: bad type
    var m0 := map[5 := ko];  // no prob
    var m1 := map[ko := 5];  // error: bad type
  }
}
