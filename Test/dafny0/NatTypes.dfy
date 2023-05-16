// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M(n: nat) {
  assert 0 <= n;
}

method Main() {
  M(25);
  M(-25);  // error: cannot pass -25 as a nat
}

class MyClass {
  var f: nat;

  method CheckField(x: nat, y: int)
    requires 0 <= y;
    modifies this;
  {
    var y: nat := y;

    assert 0 <= f;
    while (0 < y)
    {
      f := f + 1;
      if (15 < f) {
        f := f - 12;
      }
      y := y - 1;
    }
    assert 0 <= f;

    f := x;  // no problem
    f := x + 3;  // no problem here either
    f := x - 3;  // error: cannot prove RHS is a nat
  }
}

method Generic<T>(i: int, t0: T, t1: T) returns (r: T) {
  if (0 < i) {
    var n: nat := 5;
    if
    case true =>
      var j := Generic(i-1, n, -4);  // error: the type parameter is inferred as nat, but -4 is not a nat
      assert 0 <= j;
    case true =>
      var j := Generic(i-1, n, 4);
      assert 0 <= j;  // fine, since type parameter was inferred as nat in previous call
    case true =>
      var j := Generic(i-1, n as int, -4);  // now, the type parameter is inferred as int
      assert 0 <= j;  // error: result may not be a nat
    case true =>
      var j := Generic<int>(i-1, n, -4);
      assert 0 <= j;  // error: result may not be a nat
  }
  r := t1;
}

method HenEric<T>(i: int, t0: T, t1: T) returns (r: T) {
  if (0 < i) {
    var n: nat := 5;
    if
    case true =>
      var q := FenEric(n, -4);  // error: type parameter is inferred as nat, but -4 is not a nat
      assert 0 <= q;
    case true =>
      var q := FenEric(n, 4);
      assert 0 <= q;  // fine, since type parameter was inferred as nat in previous call
    case true =>
      var q := FenEric(n as int, -4);  // now, the type parameter is inferred as int
      assert 0 <= q;  // error: result isn't a nat
    case true =>
      var q := FenEric<int>(n, -4);
      assert 0 <= q;  // error: result isn't a nat
  }
  r := t1;
}

function FenEric<T>(t0: T, t1: T): T
{
  t1
}

datatype Pair<T> = Pr(T, T)

method K(n: nat, i: int) {
  match (Pair.Pr(n, i)) {
    case Pr(k, l) =>
      assert k == n;  // fine: although the type of k is int, we know it's equal to n
      assert 0 <= k;
      assert 0 <= l;  // error: l is an int
  }
}

datatype List<T> = Nil | Cons(nat, T, List<T>)

method MatchIt(list: List<object>) returns (k: nat)
{
  match (list) {
    case Nil =>
    case Cons(n, extra, tail) =>
      var w := MatchIt(tail);
      assert 0 <= w;
      assert 0 <= n;  // fine
      assert 0 <= n - 10;  // error: possible assertion failure
  }

  var m := Sum(list);
  assert 0 <= m;
  k := m;
}

class GenEric<T> {
  var f: T
  constructor (t: T) {
    f := t;
  }
}

function GE<T>(d: GenEric?<T>): bool { true }

method TestGenEric() {
  var ge;
  if (ge != null) {
    var b := GE(ge);
    var n: nat := ge.f;  // the generic instantiation is inferred to be nat, so this is okay
  }
}

function Sum(list: List<object>): nat
{
  match list
  case Nil => 0
  case Cons(x, y, tail) => x + Sum(tail)
}

ghost function BadSum(list: List<object>): nat
{
  match list
  case Nil => 0
  case Cons(x, y, tail) => x + BadSum(tail) - 30  // error: may not be a nat
}

ghost function Abs(x: int): nat
{
  if 0 <= x then x else -x
}

// ----- Here are tests that the type of the result value of a function is known by the
// ----- time the well-formedness of the function's specification is checked.

ghost function TakesANat(n: nat): bool
{
  n < 29
}

ghost function Naturally(): nat
  ensures TakesANat(Naturally());  // the wellformedness of this check requires
{
  17
}

ghost function Integrally_Bad(): int
  ensures TakesANat(Integrally_Bad());  // error: well-formedness check fails
{
  17
}

ghost function Integrally_Good(): int
  ensures 0 <= Integrally_Good();
  ensures TakesANat(Integrally_Good());  // here, the needed information follows from the preceding ensures clause
{
  17
}

// -------------------------------

datatype GList<G> = GNil | GCons(G, GList<G>)

method GList_Append(xs: GList<nat>, x: int) returns (ys: GList<nat>) {
  if 100 <= x {
    ys := GCons(x, xs);  // fine, result is a GList<nat> and x is a nat
  } else {
    ys := GCons(x, xs);  // error: result is a GList<nat>, but x may not be a nat
  }
}
