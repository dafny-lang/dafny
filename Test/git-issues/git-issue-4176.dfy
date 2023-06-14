// RUN: %baredafny verify %args %s > %t
// RUN: %diff "%s.expect" "%t"

method test(c: Class) {
    reveal Class.P();
    reveal Class.Q();
    
    assert c.P();
    assert c.Q();
}

class Class {
  opaque function P() : bool { true }
  opaque twostate function Q() : bool { true }
}