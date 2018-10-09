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
  
lemma Calc(x: int)
  requires A: x < 10
{
  assert B: x < 150 by { reveal A; }
  label QRS: assert TUV: x < 10 by {
    break ABC;  // error: a break is not allowed to leave the proof body
    reveal A;
  }

  calc {
    x < 200;
  ==  { reveal B;
        label XYZ:
        reveal C;  // error: C is not dominated here
        assert old@XYZ(x) == x;
      }
    x < 150;
  ==  { assert C: x < 90 by { reveal A; }
        reveal C;
      }
    x < 102;
  ==  { assert C: x < 90 by { reveal A; }  // it's okay to have another C here
      }
    x < 100;
  ==  { reveal A;}
    x < 10;
  ==  { assert old@XYZ(x) == x; }  // error: XYZ is not in scope here
    x < 100;
  ==
    { label ABC: assert DEF: x < 10 by { reveal A; } }
    { label ABC: assert DEF: x < 10 by { reveal A; } }
    x < 100;
  }
}

class C {
  var g: int
  var h: int
}
twostate lemma T3(c: C)
  requires old(c.g) == 10
  requires c.g == 20
  requires A: old(c.h) == 100
  requires B: c.h == 200
{
  reveal A, B, A, A;  // this can be a list
  reveal A, X, A, A;  // error: C not defined
}
