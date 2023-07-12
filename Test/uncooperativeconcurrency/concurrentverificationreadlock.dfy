// RUN: %exits-with 4 %baredafny verify --concurrent %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  var x: nat
}

method TowardsZero(a: A, b: A)
  requires readLocked(a) && readLocked(b)
  modifies a, b
  ensures a.x == b.x && a.x >= 0
{
  if(a.x > 0) {
    a.x := a.x - 1; // Error: cannot prove that a is modifyLocked
                    // In this branch only, we assume modifyLocked(a)
    a.x := a.x + 0; // OK then here
  } else {
  }
  // Here it's not assumed that a is modifyLocked because it was not in the else branch
  // But it is readLocked so its value does not change.
  b.x := a.x;       // Error: cannot prove that b is modifyLocked
  if a.x != b.x {
    print 1/0;      // Ok, because, a being readLocked, its value is the same.
  }
  assert a.x == b.x && a.x >= 0; // OK
}