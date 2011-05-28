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
