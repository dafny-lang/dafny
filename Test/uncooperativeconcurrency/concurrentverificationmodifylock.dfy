// RUN: %baredafny verify --concurrent %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  var x: int
}

method TowardsZero(a: A, b: A)
  requires modifyLocked(a) && modifyLocked(b)
  modifies a, b
  ensures a.x == b.x && a.x >= 0
{
  if(a.x > 0) {
    a.x := a.x - 1; // OK
    a.x := a.x + 0; // OK
  } else {
  }
  b.x := a.x;       // OK
  if a.x != b.x {
    print 1/0;      // Ok
  }
  assert a.x == b.x && a.x >= 0; // OK
}