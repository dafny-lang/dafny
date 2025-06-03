// RUN: %verify --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: int
  var y: int
  const c: int
  
  method InsideTest() {
    assert `x == this`x;
  }
  
  function ReadTest(): int 
    reads `x 
  {
    x
  }
}

method TestClass(t1: Test, t2: Test, t3: Test, b: bool, c: bool) {
  ghost var memoryLocation: (object, field) := t1`x;
  assert memoryLocation.0 == t1;
  assert (t2`c).0 == t2;
  ghost var allTs: set<object> := {t1, t2};
  ghost var setMems: set<(object, field)> := {t1`x,t2`x};
  assert setMems == set t: Test <- allTs :: t`x;
  ghost var seqMems: seq<(object, field)> := [t1`x,t2`x];
  assert t1`x in setMems;
  assert t2`x in setMems;


  ghost var m: (object, field) := if c then (if b then t1`x else t2`x) else t3`x;
  ghost var m2: (object, field) := if c then (if b then t1 else t2)`x else t3`x;
  assert m == m2;
  ghost var m3bis: set<(object, int)> := if c then set t: Test <- {t1, t2} :: (t, t.x) else set t: Test <- {t1} :: (t, t.x);
  ghost var m3: set<(object, field)> := if c then {t1, t2}`x else {t3}`x;
}

opaque function ReadFirstElement(a: array<int>): int
  requires a.Length >= 1
  reads a`[0]
{
  a[0]
}

method ModifyArray(a: array<int>, i: nat)
  requires a.Length >= 2
  requires 0 <= i < a.Length
  modifies a`[i]
{
  a[i] := 3;
}


method TestArray(a: array<int>, c: bool)
  requires a.Length >= 2
  modifies a
{
  ghost var m: (object, field) := a`[0];
  ghost var m2: (object, field) := a`[1];
  var c := ReadFirstElement(a);
  a[1] := 2;
  ModifyArray(a, 1);
  assert c == ReadFirstElement(a);
}

method TestArray2(a: array2<int>, c: bool)
  requires a.Length0 >= 1
  requires a.Length1 >= 1
{
  ghost var m := a`[0, 0];
}


class InScopeLocations {
  var x: int
  var y: int
  var z: int
  method Test()
    modifies {`x, `z}
  {
    assert `x == this`x;
  }
  method TestTest()
    modifies this
  {
    Test();
    assert old(y) == y;
  }
}

method TestClass2(t1: Test, t2: Test)
  modifies {t1, t2}`x
  modifies [t1, t2]`x
  modifies multiset{t1, t1, t2}`x
{
  t1.x := 3;
}

method ModifyArray2(a: array<int>, a2: array<int>)
  requires a.Length >= 2 && a2.Length >= 2
  modifies {a, a2}`[0]
  modifies [a, a2]`[0]
  modifies multiset{a, a, a2}`[0]
{
  var _ := a`[0];
  a[0] := 3;
}