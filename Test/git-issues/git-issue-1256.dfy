// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function f<X(0)>(): X
{
  var x: X :| true;
  x
}

type low_int = t | 0 <= t < 256
type high_int = t | 1000 <= t < 2000 witness 1000

method False()
  // Regression: the following postcondition was once provable
  ensures false
{
  var x: int := f();
  var y: low_int := f();
  var z: high_int := f();
  // Regression: the following assertions were once provable
  assert x == y; // error
  assert x == z; // error
}

// -----

class C<X(0)> {
  static ghost predicate P<Y>(n: nat, y: Y)

  static ghost function F(k: nat, x: X): nat
    requires P(k, x)
  {
    var n :| 0 <= n && P(n, x);
    n
  }

  static ghost function G(p: (nat, X) -> bool, k: nat, x: X): nat
    requires p(k, x)
  {
    var n :| 0 <= n && p(n, x);
    n
  }

  static const c: X

  static ghost function H(Q: (nat, bool) -> bool, k: nat): nat
    requires Q(k, true)
  {
    var n :| 0 <= n && Q(n, c == c);
    n
  }

  static ghost function S<Y>(y: Y): set<Y> { {y} }

  static ghost function I(x: X): nat
  {
    var n :| 0 <= n && x in set z | z in S(x);
    if x in S(x) then n else n + 1
  }
}

ghost function Z0<U(0)>(): int
{
  var n :| 0 <= n < 100 && n < var u: U :| true; 200;
  n
}

ghost function Z1<U(0)>(uu: U): int
{
  var n :| 0 <= n < 100 && uu == var u: U := uu; u;
  n
}

ghost function Z2<U(0)>(uu: U): int
{
  var n :| 0 <= n < 100 && 3 == var u: U := uu; 3;
  n
}

ghost function Z3<U>(c: Clx): int
{
  var n :| n == var cc: MyClx<U> := c; 5;
  12
}

class Clx { }
type MyClx<U> = c: Clx | true witness *

ghost function A0<U>(c: Clx): int
{
  var n :| n == if c is MyClx<U> then 3 else 4;
  n
}

ghost function A1<U>(o: object, c: MyClx<U>): object
  requires o == c
{
  var n: object :| n == o as MyClx<U>;
  n
}

datatype Datatype = DX | DY(o: object)

ghost function M<U>(dt: Datatype): int
  requires dt.DX?
{
  var n :| n == match dt case DX => 2 case DY(o: MyClx<U>) => 3;
  n
}

ghost function SE<X(0)>(): int {
  var n :| n == calc { 2; { var x: X; } 2; } 20;
  n
}
