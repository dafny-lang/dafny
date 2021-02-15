// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var d: D?
  const k: int
}
class D {
  var b: bool
}

method Field(c: C)
  modifies c
  requires c.d != null
{
  c.d := null;
  label L:
  assert c.d == old@L(c.d) == null != old(c.d);
  // The following errors were once not properly checked
  if
  case true =>
    ghost var x := old@L(c.d.b);  // error: null dereference error
  case true =>
    assert old@L(c.d.b) || !old@L(c.d.b);  // error (x2): null dereference error
}

method Array(arr: array<D?>, i: nat)
  requires i < arr.Length && arr[i] != null
  modifies arr
{
  arr[i] := null;
  label L:
  assert arr[i] == old@L(arr[i]) == null != old(arr[i]);
  // The following errors were once not properly checked
  if * {
    ghost var x := old@L(arr[i].b);  // error: null dereference error
  } else {
    assert old@L(arr[i].b) || !old@L(arr[i].b);  // error (x2): null dereference error
  }
}

method MultiArray(m: array2<D?>, i: nat, j: nat)
  requires i < m.Length0 && j < m.Length1 && m[i, j] != null
  modifies m
{
  m[i, j] := null;
  label L:
  assert m[i, j] == old@L(m[i, j]) == null != old(m[i, j]);
  // The following errors were once not properly checked
  if * {
    ghost var x := old@L(m[i, j].b);  // error: null dereference error
  } else {
    assert old@L(m[i, j].b) || !old@L(m[i, j].b);  // error (x2): null dereference error
  }
}

method AllocField(c: C)
  modifies c
{
  c.d := null;
  label L:
  var nd := new D;
  if * {
    ghost var x := old(nd.b);  // error: receiver must be allocated in state L
  } else {
    ghost var x := old@L(nd.b);  // error: receiver must be allocated in state L
  }
}
