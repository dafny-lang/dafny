// RUN: echo 'lit should ignore this file'

module A {
  class B {
    method C(x: Included.X)
      requires x.Z?
    {
      assert true;
    }
  }
}
