// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C<U(==)> {
  method M<T>(x: T, u: U) returns (y: T)
    ensures x == y && u == u
  {
    y := x;
  }

  function method F<X(==)>(x: X, u: U): bool
  {
    x == x && u == u
  }

  method Main(u: U)
  {
    var t := F(3,u) && F(this,u);
    var kz := M(t,u);
    var a := G();
    assert kz && (a || !a);
  }
  method G<Y>() returns (a: Y)
}

class SetTest {
  method Add<T>(s: set<T>, x: T) returns (t: set<T>)
    ensures t == s + {x}
  {
    t := s + {x};
  }

  method Good()
  {
    var s := {2, 5, 3};
    var t := Add(s, 7);
    assert {5,7,2,3} == t;
  }

  method Bad()
  {
    var s := {2, 50, 3};
    var t := Add(s, 7);
    assert {5,7,2,3} == t;  // error
  }
}

class SequenceTest {
  method Add<T>(s: seq<T>, x: T) returns (t: seq<T>)
    ensures t == s + [x]
  {
    t := s + [x];
  }

  method Good()
  {
    var s := [2, 5, 3];
    var t := Add(s, 7);
    assert [2,5,3,7] == t;
  }

  method Bad()
  {
    var s := [2, 5, 3];
    var t := Add(s, 7);
    assert [2,5,7,3] == t || [2,5,3] == t;  // error
  }
}

// -------------------------

class CC<T(0)> {
  var x: T

  method M(c: CC<T>, z: T) returns (y: T)
    modifies this
    ensures y == c.x && x == z
  {
    x := c.x;
    x := z;
    y := c.x;
  }
}

class CClient {
  method Main() {
    var c := new CC<int>;
    var k := c.x + 3;
    if c.x == c.x {
      k := k + 1;
    }
    var m := c.x;
    if m == c.x {
      k := k + 1;
    }
    c.x := 5;
    c.x := c.x;
    var z := c.M(c, 17);
    assert z == c.x;
  }
}

// -------------------------

function IsCelebrity<Person>(c: Person, people: set<Person>): bool
  requires c == c || c in people
{
  false
}

method FindCelebrity3(people: set<int>, ghost c: int)
  requires IsCelebrity(c, people)  // once upon a time, this caused the translator to produce bad Boogie
{
  ghost var b: bool;
  b := IsCelebrity(c, people);
  b := F(c, people);
}

function F(c: int, people: set<int>): bool
  requires IsCelebrity(c, people)
{
  false
}
function RogerThat<G>(g: G): G
{
  g
}

function Cool(b: bool): bool
{
  b
}

function Rockin'<G>(g: G): G
{
  var h := g;
  h
}

function Groovy<G>(g: G, x: int): G
{
  var h := g;
  if x == 80 then
    RogerThat(h)
  else
    [h][0]
}

method IsRogerCool(n: int)
  requires RogerThat(true)  // once upon a time, this caused the translator to produce bad Boogie
{
  if * {
    assert Cool(2 < 3 && n < n && n < n+1);  // the error message here will peek into the argument of Cool
  } else if * {
    assert RogerThat(2 < 3 && n < n && n < n+1);  // same here; cool, huh?
  } else if * {
    assert Rockin'(false);  // error
  } else if * {
    assert Groovy(n < n, 80);  // error
  } else if * {
    assert Groovy(n + 1 <= n, 81);  // error
  }
}

method LoopyRoger(n: int)
{
  var i := 0;
  while i < n
    invariant RogerThat(0 <= n ==> i <= n)
  {
    i := i + 1;
  }
  i := 0;
  while i < n
    invariant RogerThat(0 <= n ==> i <= n)  // error: failure to maintain loop invariant
  {
    i := i + 2;
  }
}

// ----------------------

class TyKn_C<T(0)> {
  var x: T
  function G(): T
    reads this
  {
    x
  }
  method M() returns (t: T)
  {
    return x;
  }
}

class TyKn_K {
  function F(): int { 176 }
}

method TyKn_Main(k0: TyKn_K?) {
  var c := new TyKn_C<TyKn_K?>;
  var k1: TyKn_K?;

  assert k0 != null ==> k0.F() == 176;
  assert k1 != null ==> k1.F() == 176;

  assert c.x != null ==> c.x.F() == 176;  // the Dafny encoding needs the canCall mechanism to verify this
  assert c.G() != null ==> c.G().F() == 176;  // ditto
  var k2 := c.M();
  assert k2 != null ==> k2.F() == 176;  // the canCall mechanism does the trick here, but so does the encoding
                                        // via k2's where clause
}

// ------------------- there was once a bug in the handling of the following example

module OneLayer
{
  datatype wrap<V> = Wrap(V)
}

module TwoLayers
{
  import OneLayer
  datatype wrap2<T> = Wrap2(get: OneLayer.wrap<T>)

  function F<U>(w: wrap2<U>) : OneLayer.wrap<U>
  {
    match w
    case Wrap2(a) => a
  }
  function G<U>(w: wrap2<U>) : OneLayer.wrap<U>
  {
    match w
    case Wrap2(a) => w.get
  }
  function H<U>(w: wrap2<U>) : OneLayer.wrap<U>
  {
    w.get
  }
}

// ---------------------------------------------------------------------

datatype List<T> = Nil | Cons(T, List)
predicate InList<T>(x: T, xs: List<T>)
predicate Subset<T(!new)>(xs: List, ys: List)
{
  forall x :: InList(x, xs) ==> InList(x, ys)
}
ghost method ListLemma_T<T(!new)>(xs: List, ys: List)
  requires forall x :: InList(x, xs) ==> InList(x, ys)
{
  assert Subset(xs, ys);
}
ghost method ammeLtsiL_T(xs: List, ys: List)
  requires Subset(xs, ys)
{
  assert forall x :: InList(x, xs) ==> InList(x, ys);
}
ghost method ListLemma_int(xs: List<int>, ys: List<int>)
  requires forall x :: InList(x, xs) ==> InList(x, ys)
{
  assert Subset(xs, ys);
}
ghost method ammeLtsiL_int(xs: List<int>, ys: List<int>)
  requires Subset(xs, ys)
{
  assert forall x :: InList(x, xs) ==> InList(x, ys);
}

// -------------- auto filled-in type arguments for collection types ------

function length(xs: List): nat
{
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + length(tail)
}

function elems(xs: List): set
{
  match xs
  case Nil => {}
  case Cons(x, tail) => {x} + elems(tail)
}

function Card(s: set): nat
{
  |s|
}

function Identity(s: set): set
{
  s
}

function MultisetToSet(m: multiset): set
{
  if |m| == 0 then {} else
  var x :| x in m; MultisetToSet(m - multiset{x}) + {x}
}

function SeqToSet(q: seq): set
{
  if q == [] then {} else {q[0]} + SeqToSet(q[1..])
}

datatype Pair<T(==),U(==)> = MkPair(0: T, 1: U)

method IdentityMap(s: set<Pair>) returns (m: map)
{
  m := map[];
  var s := s;
  while s != {}
    decreases s
  {
    var p :| p in s;
    m, s := m[p.0 := p.1], s - {p};
  }
}

// -------------- auto filled-in type arguments for array types ------

module ArrayTypeMagic {
  method M(a: array2)
  {
  }

  method F(b: array) returns (s: seq)
  {
    return b[..];
  }

  datatype ArrayCubeTree<T> = Leaf(array3) | Node(ArrayCubeTree, ArrayCubeTree)
  datatype AnotherACT<T> = Leaf(array3) | Node(AnotherACT, AnotherACT)
  datatype OneMoreACT<T,U> = Leaf(array3) | Node(OneMoreACT, OneMoreACT)

  function G(t: ArrayCubeTree): array3
  {
    match t
    case Leaf(d) => d
    case Node(l, _) => G(l)
  }

  datatype Nat = Zero | Succ(Nat)

  datatype List<T> = Nil | Cons(T, List)

  datatype Cell<T> = Mk(T)
  datatype DList<T,U> = Nil(Cell) | Cons(T, U, DList)
}

// -------------- regression test for parsing ------

module ParseGenerics {
  function F<X>(x: X): int

  type MyType

  ghost method M() {
    var pair := (F<MyType>, 5);  // previously, this had not parsed
    var pair' := ((F<MyType>), 5);  // this was a workaround
  }

  datatype List<Y> = Nil | Cons(Y, List)

  function Many(n: List): int
  {
    match n
    case Nil => 18
    case Cons(_, tail) => Many(tail)
  }

  lemma TestA(u: real) {
    var xs := Cons(u, Cons(u, Cons(u, Cons(u, Nil))));
    assert Many(xs) == 18;  // error: would not to unroll the function more
  }

  lemma TestB(u: real) {
    var xs := Cons(u, Cons(u, Cons(u, Cons(u, Nil))));
    // the following attribute previously caused a parsing error
    assert {:fuel Many<real>, 10} Many(xs) == 18;  // yes
  }
}

// -------------- regression test: method call where callee is in a different class with type parameters ------

module TypeSubstitutionInModifiesClause {
  class C<T> {
    ghost const Repr: set<object>
    constructor ()
      ensures fresh(Repr)
    method Update()
      modifies Repr
  }

  method Client() {
    var c := new C<int>();
    // The following call once caused malformed Boogie, because of a missing type substitution.
    c.Update();
  }
}
