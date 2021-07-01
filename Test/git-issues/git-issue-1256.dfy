// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f<X(0)>(): X
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
  static predicate P<Y>(n: nat, y: Y)

  static function F(k: nat, x: X): nat
    requires P(k, x)
  {
    var n :| 0 <= n && P(n, x);
    n
  }

  static function G(p: (nat, X) -> bool, k: nat, x: X): nat
    requires p(k, x)
  {
    var n :| 0 <= n && p(n, x);
    n
  }

  static const c: X

  static function H(Q: (nat, bool) -> bool, k: nat): nat
    requires Q(k, true)
  {
    var n :| 0 <= n && Q(n, c == c);
    n
  }

  static function S<Y>(y: Y): set<Y> { {y} }

  static function I(x: X): nat
  {
    var n :| 0 <= n && x in set z | z in S(x);
    if x in S(x) then n else n + 1
  }
}
