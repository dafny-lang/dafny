// RUN: %diff "%s" "%s"

module A {
  class B {
    method C(x: Included.X)
      requires x.Z?
    {
      assert true;
    }
  }
}
