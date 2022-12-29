// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
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
    ghost var x := old(nd.b);  // error: receiver must be allocated in old state
  } else {
    ghost var x := old@L(nd.b);  // error: receiver must be allocated in state L
  }
}

method AllocArray(c: C)
  modifies c
{
  c.d := null;
  label L:
  var arr := new real[5];
  if * {
    ghost var x := old(arr[2]);  // error: array must be allocated in old state
  } else {
    ghost var x := old@L(arr[2]);  // error: array must be allocated in state L
  }
}

method AllocMatrix(c: C)
  modifies c
{
  c.d := null;
  label L:
  var m := new real[5, 5];
  if * {
    ghost var x := old(m[2, 0]);  // error: array must be allocated in old state
  } else {
    ghost var x := old@L(m[2, 0]);  // error: array must be allocated in state L
  }
}

method ArrayNullCheckRegression0(arr: array?<real>, m: array2?<real>, a10: Array10, m1010: Matrix1010)
{
  var x := arr[2];  // error (x2): array may be null, index out of bounds
  var y := m[2, 3];  // error (x3): array may be null, indices out of bounds
}

type Array10 = a: array?<real> | a == null || a.Length == 10
type Matrix1010 = a: array2?<real> | a == null || (a.Length0 == a.Length1 == 10)

method ArrayNullCheckRegression1(arr: Array10, m: Matrix1010)
{
  var x := arr[2];  // error: array may be null
  var y := m[2, 3];  // error: array may be null
}
