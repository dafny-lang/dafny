// RUN: %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

trait T {

  ghost function Modifies(): set<object>

  method Foo()
    modifies Modifies()
}

class {:compile false} C extends T {

  const Repr: set<object>

  ghost function Modifies(): set<object> {
    Repr
  }

  method Foo()
    modifies Modifies()
}
