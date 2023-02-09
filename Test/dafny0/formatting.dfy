// RUN: %baredafny format --print "%s" > "%t"
// RUN: %diff "%s" "%t"

include "formattinginclude.dfy"

module A {
  class B {
    method C(x: Included.X)
      requires x.Z?
    {
      assert true;
    }
  }
}
