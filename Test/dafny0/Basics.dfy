class Global {
  static function G(x: int): int { x+x }
  static method N(x: int) returns (ghost r: int)
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

//  call r := Global.N(k);
//  assert r == s;

  call r := g.N(k);
  assert r == s;
  call r := h.N(k);
  assert r == s;

  g := null;
  call r := g.N(k);
  assert r == s;

//  call r := Global.N(r);
  if (k == 0) {
    assert r == s;
  } else {
//    assert r == s;  // error: G(k) and G(k+k) are different
  }
}
