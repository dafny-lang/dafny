// RUN: %exits-with 5 %baredafny format --use-basename-for-filename --check "%s" > "%t"
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
