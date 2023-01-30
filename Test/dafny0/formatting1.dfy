// RUN: %baredafny format --use-basename-for-filename --print "%s" "%S/formatting1-2.dfy" "%S/formatting1-3.dfy" > "%t"
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
