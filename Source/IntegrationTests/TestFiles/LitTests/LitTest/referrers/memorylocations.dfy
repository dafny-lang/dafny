class Test {
  var x: int
  const c: int
}

method TestClass(t1: Test, t2: Test, t3: Test, b: bool, c: bool) {
  ghost var memoryLocation := t1`x;
  assert memoryLocation.0 == t1;
  assert (t2`c).0 == t2;
  ghost vars allTs := {t1, t2};
  ghost var setMems: set<(object, objectfield)> := {t1`x,t2`x};
  assert setMems == set t <- allTs :: t`x;
  ghost var seqMems: seq<(object, objectfield)> := [t1`x,t2`x];
  assert set r <- setMems :: r.0 == {t1, t2};
  assert (set r <- seqMems) == setMems;
  
  ghost var m: (object, objectfield) := if c then (if b then t1`x else t2`x) else t3`x;
  ghost var m2: (object, objectfield) := if c then (if b then t1 else t2)`x else t3`x;
  assert m == m2;
}

opaque function ReadFirstElement(a: array<int>)
  requires a.Length >= 1
  reads {a`[0]}
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
  ghost var m: (object, objectfield) := a`[0];
  ghost var m: (object, objectfield) := a`[1];
  var c := ReadFirstElement(a);
  a[1] := 2;
  ModifyArray(a, 1);
  assert c == ReadFirstElement(a);
}

method TestArray2(a: array2<int, int>, c: bool)
  requires a.Length1 >= 1
  requires a.Length2 >= 1
{
  ghost var m := a`[0, 0];
}