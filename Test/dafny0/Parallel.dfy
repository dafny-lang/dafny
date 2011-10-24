class C {
  var data: int;
  var st: set<object>;
}

// This method more or less just tests the syntax, resolution, and basic verification
method ParallelStatement_Resolve(
    a: array<int>,
    spine: set<C>,
    Repr: set<object>,
    S: set<int>
  )
  requires a != null && null !in spine;
  modifies a, spine;
{
  parallel (i: int | 0 <= i < a.Length && i % 2 == 0) {
    a[i] := a[(i + 1) % a.Length] + 3;
  }

  parallel (o | o in spine) {
    o.st := o.st + Repr;
  }

  parallel (x, y | x in S && 0 <= y+x < 100) {
    Lemma(x, y);
  }

  parallel (p | 0 <= p)
    ensures F(p) <= Sum(p) * (p-1) + 100;  // error (no connection is known between F and Sum)
  {
    assert 0 <= G(p);
    ghost var t;
    if (p % 2 == 0) {
      assert G(p) == F(p+2);  // error (there's nothing that gives any relation between F and G)
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
function G(x: int): nat
function H(x: int, y: int): int
function Sum(x: int): int

// ---------------------------------------------------------------------

method M0(S: set<C>)
  requires null !in S;
  modifies S;
  ensures forall o :: o in S ==> o.data == 85;
  ensures forall o :: o != null && o !in S ==> o.data == old(o.data);
{
  parallel (s | s in S) {
    s.data := 85;
  }
}

method M1(S: set<C>, x: C)
  requires null !in S && x in S;
{
  parallel (s | s in S)
    ensures s.data < 100;
  {
    assume s.data == 85;
  }
  if (*) {
    assert x.data == 85;  // error (cannot be inferred from parallel ensures clause)
  } else {
    assert x.data < 120;
  }

  parallel (s | s in S)
    ensures s.data < 70;  // error
  {
    assume s.data == 85;
  }
}

method M2() returns (a: array<int>)
  ensures a != null;
  ensures forall i,j :: 0 <= i < a.Length/2 <= j < a.Length ==> a[i] < a[j];
{
  a := new int[250];
  parallel (i: nat | i < 125) {
    a[i] := 423;
  }
  parallel (i | 125 <= i < 250) {
    a[i] := 300 + i;
  }
}
