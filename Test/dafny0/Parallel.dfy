/*
method ParallelStatement_Syntax()
{
  parallel (i: int | 0 <= i < a.Length && i % 2 == 0) {
    a[i] := a[(i + 1) % a.Length] + 3;
  }

  parallel (o | o in spine) {
    o.f := o.f + Repr;
  }

  parallel (x, y | x in S && 0 <= y+x < 100) {
    Lemma(x, y);
  }

  parallel (p | 0 <= p)
    ensures F(p) <= Sum(p) * (p-1) + 100;
  {
    assert G(p);
    ghost var t;
    if (p % 2 == 0) {
      assert G(p) == F(p+2);
      t := p*p;
    } else {
      assume H(p, 20) < 100;  // don't know how to justify this
      t := p;
    }
    PowerLemma(p, t);
    t := t + 1;
    PowerLemma(p, t);
  }
}
*/

class C {
  var f: set<object>;
}

method ParallelStatement_Resolve(
    a: array<int>,
    spine: set<C>,
    Repr: set<object>,
    S: set<int>
  )
  requires a != null;
  modifies a, spine;
{
  parallel (i: int | 0 <= i < a.Length && i % 2 == 0) {
    a[i] := a[(i + 1) % a.Length] + 3;
  }

  parallel (o | o in spine) {
    o.f := o.f + Repr;
  }

  parallel (x, y | x in S && 0 <= y+x < 100) {
    Lemma(x, y);
  }

  parallel (p | 0 <= p)
    ensures F(p) <= Sum(p) * (p-1) + 100;
  {
    assert 0 <= G(p);
    ghost var t;
    if (p % 2 == 0) {
      assert G(p) == F(p+2);
      t := p*p;
    } else {
      assume H(p, 20) < 100;  // don't know how to justify this
      t := p;
    }
    PowerLemma(p, t);
    t := t + 1;
    PowerLemma(p, t);
  }
}

method Lemma(x: int, y: int)
ghost method PowerLemma(x: int, y: int)

function F(x: int): int
function G(x: int): int
function H(x: int, y: int): int
function Sum(x: int): int
