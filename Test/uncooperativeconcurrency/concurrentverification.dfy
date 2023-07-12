// RUN: %exits-with 4 %baredafny verify --concurrent %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  var x: nat
}

method TowardsZero(a: A, b: A)
  modifies a, b
  ensures a.x == b.x && a.x >= 0
{
  if(a.x > 0) {
    a.x := a.x - 1; // Error: cannot prove that a is modifyLocked
  } else {
  }
  // Here it's not assumed that a is modifyLocked or readLocked because it was not in the else branch
  b.x := a.x;       // Error: cannot prove that b is modifyLocked
  if a.x != b.x {
    print 1/0; // Fails to verify because cannot prove that a.x != b.x
               // because, although b is assumed to be modifyLocked, a is not.
  }
  assert a.x == b.x && a.x >= 0; // Fails to verify
}