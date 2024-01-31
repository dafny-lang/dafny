// RUN: %testDafnyForEachResolver "%s"


module A {
  ghost predicate F(x: int) { true }
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
