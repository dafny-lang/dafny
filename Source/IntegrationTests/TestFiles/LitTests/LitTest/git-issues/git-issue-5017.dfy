// RUN: %testDafnyForEachResolver "%s"

trait A {
  ghost predicate Valid()
}

trait B extends A {
  ghost opaque predicate Valid() { true }
}

method TestByRequires(b: B)
  requires b.Valid()
{
  var a: A := b;
  assert a.Valid();
}

method TestByReveal(b: B) {
  var a: A := b;
  assert a.Valid() by {
    reveal b.Valid();
  }
}
