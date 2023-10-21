// RUN: %baredafny format --check "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class B {
    method C(x: Included.X)
      requires x.Z?
    {
      assert true;
    }
  }
}
