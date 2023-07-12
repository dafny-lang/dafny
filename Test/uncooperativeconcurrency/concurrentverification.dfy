// RUN: %exits-with 4 %baredafny verify --concurrent %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class A {
  var x: int
}

method TowardsZero(a: A, b: A) modifies a, b ensures a.x == b.x && a.x >= 0 {
  if(a.x > 0) {
    a.x := a.x - 1;
  } else {
    a.x := 0;
  }
  b.x := a.x;
  if a.x != b.x {
    print 1/0;
  }
  assert a.x == b.x && a.x >= 0;
}