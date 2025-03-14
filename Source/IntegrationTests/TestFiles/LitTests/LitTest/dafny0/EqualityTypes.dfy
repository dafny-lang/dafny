// RUN: %exits-with 2 %verify --allow-deprecation --type-system-refresh=false --general-newtypes=false "%s" > "%t"
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
  class C ... {
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
  datatype X<T(==)> = Nil | Cons(T, X<T>)  // error: not allowed to add a type parameter to type X
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
  function F<T>(x: BulkyList<T>, y: BulkyList<T>): int
  { if x == y then 5 else 7 }  // this equality is allowed
  function G<T>(x: Dt<T>, y: Dt<T>): int
  { if x == y then 5 else 7 }  // error: the equality is not allowed, because Dt<T> may not support equality
  function G'<T(==)>(x: Dt<T>, y: Dt<T>): int
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

  function F(b: bool, ghost g: bool): int { 6 }

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

  }

  function G<Y(==)>(y: Y, z: Y): int { if y == z then 5 else 7 }

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

//--------------------------

module UnderspecifiedTypeParameters {
  method UP<T>()
  function UG<T>(): int
  method Callee<T(==)>()
  class TakesParam<U> { }

  method MPG()
  {
    var g := UG();  // error: type parameter underspecified
    UP();  // error: type parameter underspecified
  }
  method M() {
    var zs: set;  // error: type is underspecified
    Callee<(int)>();
    Callee<set>();  // error: type is underspecified
    Callee<()>();
    // The following
    Callee<TakesParam>();  // error: type is underspecified
  }
}

module EqualitySupportingTypes {
  method P<T>()
  function G<T>(): int
  class AClass<V(==),Y> {
    static function H<W,X(==)>(): bool
    static method Q<A,B(==)>()
  }

  method Callee<T(==)>()
  function FCallee<T>(): T

  datatype Dt = Dt(f: int -> int)
  codatatype Stream<T> = Cons(T, Stream)

  method M<ArbitraryTypeArg>()
  {
    Callee<Dt>();  // error:  Dt is not an equality-supporting type
    Callee<Stream<int>>();  // error: specified type does not support equality

    // set<X> is allowed in a non-ghost context only if X is equality supporting.
    // Ditto for multiset<X> and map<X,Y>.
    var s3x: set<Dt>;  // error: this type not allowed in a non-ghost context
    var is3x: iset<Dt>;  // error: this type not allowed in a non-ghost context
    var mast: multiset<ArbitraryTypeArg>;  // error: this type not allowed in a non-ghost context
    var qt: seq<Stream<int>>;  // allowed
    var mp0: map<Dt,int>;  // error: this type not allowed in a non-ghost context
    var mp1: map<int,Dt>;  // allowed
    var imp0: imap<Dt,int>;  // error: this type not allowed in a non-ghost context
    var imp1: imap<int,Dt>;  // allowed

    var S := FCallee<set>();  // this gives s:set<?>
    if 4 in S {              // this constrains the type further to be s:set<int>
    }

    var xy: set<set<int>>;
    var xz: set<set<Stream<int>>>;  // error: set type argument must support equality

    Callee<set<Stream<int>>>();  // error: cannot utter set<Stream<int>>  -- Note: language definition should be changed, because it doesn't make sense for it to talk about a type appearing in a ghost or non-ghost context. Instead, set/iset/multiset/map/imap should always be allowed to take any type argument, but these types may or may not support equality.
    var xg := G<set<Stream<int>>>();  // error: cannot utter set<Stream<int>>, because Stream<int> does not support equality

    var ac0: AClass<int,int>;
    var ac1: AClass<Stream<int>,int>;  // error: type parameter 0 is required to support equality
    var ac2: AClass<int,Stream<int>>;
    var xd0 := ac0.H<real,real>();
    var xd1 := ac1.H<Stream<real>,real>();  // error (remnant of the fact that the type of ac1 is not allowed)
    var xd2 := ac2.H<real,Stream<real>>();  // error: type parameter 1 is required to support equality
    var xe0 := ac0.H<real,real>;
    var xe1 := ac1.H<Stream<real>,real>;  // error (remnant of the fact that the type of ac1 is not allowed)
    var xe2 := ac2.H<real,Stream<real>>;  // error: type parameter 1 is required to support equality
    var xh0 := AClass<int,int>.H<real,real>();
    var xh1 := AClass<int,int>.H<Stream<real>,real>();
    var xh2 := AClass<int,int>.H<real,Stream<real>>();  // error: type parameter 1 is required to support equality
    var xk0 := AClass<real,real>.H<int,int>;
    var xk1 := AClass<Stream<real>,real>.H<int,int>;  // error: class type param 0 wants an equality-supporting type
    var xk2 := AClass<real,Stream<real>>.H<int,int>;
    AClass<Stream<int>,int>.Q<real,real>();  // error: class type param 0 wants an equality-supporting type
    AClass<int,Stream<int>>.Q<real,real>();
    AClass<int,Stream<int>>.Q<Stream<real>,real>();
    AClass<int,Stream<int>>.Q<real,Stream<real>>();  // error: method type param 1 wants an equality-supporting type

    AClass<int,set<Stream<int>>>.Q<real,real>();  // error: cannot utter "set<Stream<int>>"
    AClass<int,int>.Q<set<Stream<real>>,real>();  // error: cannot utter "set<Stream<real>>"
    var xi0 := AClass<int,set<Stream<int>>>.H<real,real>();  // error: cannot utter "set<Stream<int>>"
    var xi1 := AClass<int,int>.H<real,set<Stream<real>>>();  // error: cannot utter "set<Stream<real>>"

    var x, t, s: seq<int -> int>, fii: int -> int;
    if s == t {  // error: this comparison requires the types of s and t to be equality supporting
      x := 5;
    }
    if fii in s {  // error: this operation requires "s" to be an equality-support sequence (which it isn't)
      x := 4;
    }
    if !(fii in s) {  // error: this operation requires "s" to be an equality-support sequence (which it isn't)
      x := 3;
    }

    ghost var ghostset: set<Stream<int>> := {};  // fine, since this is ghost
    forall u | 0 <= u < 100
      ensures var lets: set<Stream<int>> := {}; lets == lets  // this is ghost, so the equality requirement doesn't apply
    {
    }

  }
}

module MoreEqualitySupportingTypes {
  type ABC
  type JustOpaque<A(==)>
  type Synonym<A(==)> = (int,A)
  type Subset<A(==)> = a: A | a == a
  method Test() {
    var a: JustOpaque<ABC>;  // error: type argument to JustOpaque must support equality
    var b: Synonym<ABC>;  // error: type argument to Synonym must support equality
    var c: Subset<ABC>;  // error: type argument to Subset must support equality
  }
}

// ----------------------------

module AlwaysOkayComparisons {
  datatype List<A> = Nil | Cons(A, List) | ICons(int, List)
  datatype TwoLists<A> = Two(List, List)
  datatype GhostRecord = GR(int, ghost int, bool)
  codatatype Co<A> = Atom(A) | CoCons(int, Co) | CoConsA(A, Co)

  method M<A>(xs: List, a: A) returns (r: bool)
  {
    var u := 6;
    r := xs == xs;  // error: cannot compare
    r := xs == Nil;
    r := xs == Cons(a, Nil);  // error: cannot compare
    r := xs == ICons(4, ICons(2, Nil));
    r := xs == ICons(2, ICons(u, Nil));
    r := xs == ICons(2, ICons(30, xs));  // error: cannot compare
  }

  method N<A>(pr: (A, List<A>), a: A, pair: TwoLists<A>) returns (r: bool)
  {
    r := pr == (a, Nil);  // error: cannot compare
    r := pair == Two(ICons(4, Nil), Nil);
  }

  method G(g: GhostRecord) returns (r: bool)
  {
    r := g == GR(5, 6, true);  // error: cannot compare
  }

  method H<A,B(==)>(c: Co<A>, d: Co<B>, a: A, b: B) returns (r: bool)
  {
    r := c == Atom(a);  // error: cannot compare
    r := d == Atom(b);
    r := d == CoCons(10, CoCons(8, Atom(b)));
  }

  method CompareDisplays<A,B>(q: seq<B>, m: map<A,B>) returns (r: int) {
    r := if q != [] && m == map[] then 3 else 5;  // allowed
  }
}

// ----------------------------

module RegressionsSeqMap {
  method M0<A>(q: seq<A>)  // this does not make A into A(==)
  {
    var s: set<A>;  // error: set<A> requires A to be equality supporting
  }
  method M1<A>(q: seq<A>, a: A) returns (r: int)  // this does not make A into A(==)
  {
    if a in q {  // error: this operation requires A to be equality supporting
      r := 10;
    }
    if a: A :| a in q {  // error: this operation requires A to be equality supporting
      r := 12;
    }
    var q': seq<A>, b: bool;
    b := q' <= q;  // error: this operation requires A to be equality supporting
  }
  method N0<A,B>(m: map<A,B>) returns (r: int)  // this infers <A(==),B>
  {
    var items := m.Items;  // error: this requires (A and) B to be equality supporting
    var keys := m.Keys;
    var values := m.Values;  // error: this requires B to be equality supporting
    ghost var gv := m.Values;
    ghost var itms := m.Items;
    gv, keys, itms := {}, {}, {};
  }
  method N1<A,B>(a: A, b: B) returns (r: int)  // this infers <A(==),B>
  {
    var m: map<A,B>;  // error: this requires A to be equality supporting
  }
}
