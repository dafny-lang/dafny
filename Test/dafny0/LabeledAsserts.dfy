// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var g: int
  var h: int
}

// Here are examples of suppressed preconditions and assertions

iterator Iter0(x: int, y: int, z: int) yields (u: int)
  requires 0 <= x
  requires Y: 0 <= y
  requires Z: 0 <= z
{
  assert 0 <= x;
  assert 0 <= y;  // error: labeled requires is suppressed
  yield 20;
  assert A: x + y == 80;  // error: may not hold
  assert B: x + y == 80;  // error: still may not hold, and the previous assert is of no help
  assert x + y == 80;  // error: still may not hold, and the previous assert is of no help
  assert x + y == 80;  // fine
  yield 30;
  assert 0 <= z;  // error: labeled requires is suppressed
}

method M0(x: int, y: int)
  requires 0 <= x
  requires Y: 0 <= y
{
  assert 0 <= x;
  assert 0 <= y;  // error: labeled requires is suppressed
}

twostate lemma T0(c: C)
  requires old(c.g) == 10
  requires c.g == 20
  requires A: old(c.h) == 100
  requires B: c.h == 200
{
  assert old(c.g) < c.g;
  assert old(c.h) < 150;  // error: labeled requires is suppressed
  assert 150 < c.h;  // error: labeled requires is suppressed
}

method Test(c: C)
  requires c.g == 0
  modifies c
{
  var local := 1;
  c.g := local;
  label A: label AA:
  assert X: c.g == local == 1;

  local, c.g := local + 1, local + 1;
  label B: label BB:
  assert Y: c.g == local == 2;

  local, c.g := local + 1, local + 1;
  assert Z: c.g == local == 3;
  
  assert old(c.g) < old@A(c.g) < old@B(c.g) < c.g;
  assert old@A(local) == 3 == old@B(local);  // true, because old does not affect local variables
}
