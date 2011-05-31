class Global {
  static function G(x: int): int { x+x }
  static method N(ghost x: int) returns (ghost r: int)
    ensures r == Global.G(x);
  {
    if {
      case true =>  r := G(x+0);
      case true =>
        var g: Global;
        r := g.G(x);
      case true =>
        var g: Global := null;
        r := g.G(x);
      case true =>
        r := Global.G(x);
    }
  }
}

method TestCalls(k: nat) {
  var g: Global, h: Global;
  assume g != h;
  ghost var r: int;
  ghost var s := Global.G(k);

  r := Global.N(k);
  assert r == s;

  r := g.N(k);
  assert r == s;
  r := h.N(k);
  assert r == s;

  g := null;
  r := g.N(k);
  assert r == s;

  r := Global.N(r);
  if (k == 0) {
    assert r == s;
  } else {
    assert r == s;  // error: G(k) and G(k+k) are different
  }
}

// ---------- chaining operators ------------------------------------

function UpTruth(j: int, k: int): bool
  requires 10 <= j < 180 < 220 <= k;
{
  0 < 2 <= 2 < j != 200 < k < k + 1
}

function DownTruth(j: int, k: int): bool
  requires k >= 220 > 180 > j >= 10;
{
  k + 1 > k > 200 != j > 2 >= 2 > 0
}

method ChallengeTruth(j: int, k: int)
  requires 80 <= j < 150 && 250 <= k < 1000;
{
  assert UpTruth(j, k);
  assert DownTruth(j, k);
  // but this is not equally true:
  assert j <= j + k != k + j + 1 < k+k+j <=/*this is the error*/ j+j+k < k+k+j+j == 2*k + 2*j == 2*(k+j);
}

// --------- multi assignments --------------------------------

class Multi {
  var x: int;
  var y: int;
}

method TestMulti(m: Multi, p: Multi)
  requires m != null && p != null;
  modifies m, p;
{
  m.x := 10;
  m.y := 12;
  p.x := 20;
  p.y := 22;
  if (*) {
    assert p.x == 20;
    assert m.x == 10;  // error: m and p may be the same
  }
  var t, u;
  u, m.x, t := 100, u + t + m.x, 200;
  m.x := 0;
  u, m.x, t := 200, u + t + m.x, 400;
  assert m.x == 300;
  if (p.x != 300) {
    p.x, m.x := m.x, p.x;
  }
  assert p.x == 300;
  if (*) {
    p.x, m.y := 10, 10;
    p.x, m.x := 8, 8;  // error: duplicate assignment (since m and p may be the same)
  }

  var a, b := new int[20], new int[30];
  a[4], b[10], a[0], a[3], b[18] := 0, 1, 2, 3, 4;
  a[4], b[b[18]] := 271, 272;
  a[4], a[b[18]] := 273, 274;  // error: duplicate assignment (since b[18] is 4)
}

class MyBoxyClass<T> {
  var f: T;
}

method TestBoxAssignment<T>(x: MyBoxyClass<int>, y: MyBoxyClass<T>, t: T)
  requires x != null && y != null;
  modifies x, y;
{
  y.f := t;
  x.f := 15;
  // all together now:
  y.f, x.f := t, 15;  // error: duplicate assignment (if T==int and x==y)
}
