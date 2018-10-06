// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma A(b: bool, m: int, n: int)
  requires m < n
  requires sea: m + 3 < n
  requires sjc: m + 5 < n
  requires sjc: m + 7 < n  // error: dominating label
  requires jfk: m + 9 < n
  requires m < n
{
  label a: assert true;
  if b {
    label x: assert true;
    label K: assert {:myAttr 30} m < n;
    label L: assert {:myAttr 30} m < n;
    label 0: assert {:myAttr 30} m < n;
    label 0: assert {:myAttr 30} m < n;  // error: dominating label
    label jfk: assert true;  // error: dominating label
  } else {
    label x: assert true;
    assert {:myAttr 30} K: m < n;
    assert {:myAttr 30} L: m < n;
    assert {:myAttr 30} 0: m < n;
    assert {:myAttr 30} 0: m < n;  // error: dominating label
    var x: int;
    assert jfk: true;  // error: dominating label
    assert old(b) == old@a(b) == old@x(b);
  }
  assert 0010: m < n;
  assert {:myAttr 30} K: m < n;
  label L:
  assert {:myAttr 30} L: m < n;  // error: dominating label
  assert old(b) == old@a(b);
  assert old(b) == old@sjc(b);
  // var r := assert NotAllowedHere: 0 <= m; 10;  // not allowed; won't parse
}

function R(u: int): int
  // requires i: 0 <= u  // not allowed; won't parse
{
  // assert NotAllowedHere: 0 <= u;  // not allowed; won't parse
  u
}

iterator Iter(x: int) yields (y: int)
  requires A: 0 <= x
  // yield requires B: 0 <= y  // not allowed; won't parse
{
  assert C: 0 <= x < |ys|;
  assert A: 0 <= x < |ys|;  // error: dominating label
  yield;
  assert C: 0 <= x < |ys|;  // error: dominating label
}

twostate predicate Twop(x: int)
  // requires A: 0 <= x  // not allowed; won't parse
{
  true
}

twostate lemma Twol(x: int)
  requires A: 0 <= x
{
}
