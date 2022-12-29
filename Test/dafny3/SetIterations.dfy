// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Count<T>(s: set<T>): int
{
  if s == {} then 0 else
    var x :| x in s;  // let x be such that "x in s"
    1 + Count(s - {x})
}

method Copy<T>(s: set<T>) returns (t: set<T>)
  ensures s == t
{
  t := {};
  var r := s;
  while r != {}
    invariant s == r + t
    decreases r
  {
    var x :| x in r;
    r, t := r - {x}, t + {x};
  }
}

method CopyFaster<T>(s: set<T>) returns (t: set<T>)
  ensures s == t
{
  t := {};
  var r := s;
  while r != {}
    invariant s == r + t
    decreases r
  {
    var p :| p != {} && p <= r;  // pick a nonempty subset of r
    r, t := r - p, t + p;
  }
}

method CopyFastest<T>(s: set<T>) returns (t: set<T>)
  ensures s == t
{
  t := s;  // :)
}

iterator Iter<T(0)>(s: set<T>) yields (x: T)
  yield ensures x in s && x !in xs[..|xs|-1]
  ensures s == set z | z in xs
{
  var r := s;
  while r != {}
    invariant forall z :: z in xs ==> z !in r  // r and xs are disjoint
    invariant s == r + set z | z in xs
  {
    var y :| y in r;
    r, x := r - {y}, y;
    yield;
    assert y == xs[|xs|-1];  // needed as a lemma to prove loop invariant
  }
}

method UseIterToCopy<T(0)>(s: set<T>) returns (t: set<T>)
  ensures s == t
{
  t := {};
  var m := new Iter(s);
  while true
    invariant m.Valid() && fresh(m._new)
    invariant t == set z | z in m.xs
    decreases s - t
  {
    var more := m.MoveNext();
    if !more { break; }
    t := t + {m.x};
  }
}
