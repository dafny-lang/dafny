// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  predicate F(x: int) { true }
}

module B {
  import I = A

  lemma Test(x: int)
    ensures I.F(x)
  {
  }

  lemma TestWrapper()
  {
    forall x {
      Test(x);
    }
  }
}
