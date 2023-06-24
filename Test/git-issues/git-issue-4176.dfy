// RUN: %baredafny verify %args %s > %t
// RUN: %diff "%s.expect" "%t"

method test(c: Class) {
    reveal Class.P();
    reveal Class.Q();
    reveal f();
    
    assert c.P();
    assert c.Q();
    assert f();
}

class Class {
  opaque function P() : bool { true }
  opaque twostate function Q() : bool { true }
}

opaque function f() : bool { true }