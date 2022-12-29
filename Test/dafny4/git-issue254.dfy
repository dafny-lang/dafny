// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Foo {}

trait InputStream {
  var x: int
  predicate Valid() reads this
  method read(b: Foo)
    requires Valid()
}

class ToyInputStream extends InputStream {
  predicate Valid() reads this {
    x == 7
  }
  // regression test: the following line once complained that preconditions have
  // to be equal or more permissive precondition than in its parent trait
  method read(b: Foo)
    requires Valid()
  { }
}
