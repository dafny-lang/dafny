method M(n: nat) {
  assert 0 <= n;
}

method Main() {
  M(25);
  M(-25);  // error: cannot pass -25 as a nat
}

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

method Generic<T>(i: int, t0: T, t1: T) returns (r: T) {
  if (0 < i) {
    var n: nat := 5;
    var j := Generic(i-1, n, -4);
    assert 0 <= j;  // error: the result is an int, not a nat
    var q := FenEric(n, -4);
    assert 0 <= q;  // error: the result is an int, not a nat
  }
  r := t1;
}

function method FenEric<T>(t0: T, t1: T): T

datatype Pair<T> = Pr(T, T);

method K(n: nat, i: int) {
  match (Pair.Pr(n, i)) {
    case Pr(k, l) =>
      assert k == n;  // fine: although the type of k is int, we know it's equal to n
      assert 0 <= k;
      assert 0 <= l;  // error: l is an int
  }
}

datatype List<T> = Nil | Cons(nat, T, List<T>);

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
  var f: T;
}

function method GE<T>(d: GenEric<T>): bool { true }

method TestGenEric() {
  var ge;
  if (ge != null) {
    var b := GE(ge);
    var n: nat := ge.f;  // error: the generic instantiation uses int, not nat
  }
}

function method Sum(list: List<object>): nat
{
  match list
  case Nil => 0
  case Cons(x, y, tail) => x + Sum(tail)
}

function BadSum(list: List<object>): nat
{
  match list
  case Nil => 0
  case Cons(x, y, tail) => x + BadSum(tail) - 30  // error: may not be a nat
}

function Abs(x: int): nat
{
  if 0 <= x then x else -x
}
