// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Array<T>
{
   var Length: nat;
}

class Test<T> {
  var a: Array<int>;
  var b: Array<T>;
  predicate valid()
      reads this, a, b;
  {
    a != null && b != null &&
    a != b &&  // this is the kind of thing the liberal equalty rules are designed to support
    a.Length == b.Length
  }
}

method m0<T, U>(t: T, u: U, x: int)
   requires t != u; // error: Cannot compare type parameters (can only compare reference types that could be the same)
   requires u != x; // error: the liberal equality rules apply only if the top-level type is a reference type
{
}

method m1<T>(t: array<T>, a: array<int>, b: array3<T>, c: array3<int>)
   requires t != null && a != null && b != null && c != null;
   requires t != a && t.Length == a.Length;
   requires b != c && b.Length0 == c.Length0 && b.Length1 == c.Length1 && b.Length2 == c.Length2;
   requires t != b;  // error: these types are never the same
   requires a != c;  // error: these types are never the same
   requires t != c;  // error: these types are never the same
   requires a != b;  // error: these types are never the same
{
}


class Weird<T, U, V> { }

method m2<T, V>(a: Weird<T, int, V>, b: Weird<T, bool, V>)
   requires a == b; // error: second parameter can't be both bool and int.
{
}

method m3<T, U, V>(a: Weird<T, U, V>, b: Weird<T, bool, V>)
  requires a == b;
{
}

method m4<T>(a: Weird<T, T, bool>, b: Weird<T, bool, T>, c: Weird<T, int, T>)
  requires b != c;  // error: this is like in m2 above
  requires a != b;  // the types of a and b would be the same if T := bool
  requires a != c;  // this is allowed by the liberal equality rules, which are simple minded;
                    // but there isn't actually any way that the types of a and c could be the same
{
}

// Just to make sure nothing went wrong.
method m5(a: array<int>, b: array<bool>)
   requires a == b; // error: never equal
{
}

iterator Iter<T>() { }

method m6<T>(a: Iter<T>, b: Iter<int>)
  requires a != b;
{
}

method m7<T>(a: T ~> int, b: int ~> T, c: int ~> int)
  requires a != c;  // error: arrow types don't fall under the liberal equality rules
  requires b != c;  // error: ditto
{
}

type Syn<U> = Weird<U, U, int>

method m8<T,U>(a: Weird<int,int,int>, b: Syn<int>, c: Weird<T, bool, U>, d: Syn<T>, e: Syn<bool>)
  requires a != b;  // no prob -- the types are always equal
  requires b != d;  // allowed
  requires c != d;  // allowed
  requires b != e;  // error: these can't be the same type, ever
{
}

datatype List<X> = Nil | Cons(X, List<X>)
type ListSynonym<X,Y> = List<Y>
type Wrapper<T> = T

method m9<T>(a: array<List<int>>, b: array<List<bool>>,
             c: array<ListSynonym<T,int>>, d: array<ListSynonym<bool,int>>,
             e: array<ListSynonym<int,T>>, f: array<ListSynonym<real,Wrapper<int>>>)
  requires a != b;  // error
  requires a != c;
  requires b != c;  // error
  requires c != d;
  requires a != e;  // error
  requires b != e;  // error
  requires d != e;  // error
  requires a != f;
  requires b != f;  // error
{
}
