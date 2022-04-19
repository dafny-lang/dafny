// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test that it is known that a value of a (!new) type is allocated in every state.

class C { }
type Y(!new)
type Z(!new)<A, B(!new)>

twostate lemma R<X(!new)>(new c: C, new x: X, new y: Y, new z: Z<object, int>, new i: int) {
  assert allocated(c);
  assert allocated(x);
  assert allocated(y);
  assert allocated(z);
  assert allocated(i);
  assert old(allocated(c)); // error: this may not hold
  assert old(allocated(x));
  assert old(allocated(y));
  assert old(allocated(z));
  assert old(allocated(i));
}

class Class<X(!new), Y> {
  twostate lemma R(new x: X, new y: Y) {
    assert old(allocated(x));
    assert old(allocated(y)); // error: this may not hold
  }
}

datatype Datatype<X(!new), Y> = Ctor(X) {
  twostate lemma R(new x: X, new y: Y) {
    assert old(allocated(x));
    assert old(allocated(y)); // error: this may not hold
  }
}

class Cell<X> {
  var x: X
  constructor (x: X) {
    this.x := x;
  }
}

iterator Iter<X(!new), Y>(x: X, y: Y) {
  var c := new Cell<X>(x);
  var d := new Cell<Y>(y);
  var cx, dx := c.x, d.x;
  assert old(allocated(cx));
  assert old(allocated(dx)); // error: this may not hold
}
