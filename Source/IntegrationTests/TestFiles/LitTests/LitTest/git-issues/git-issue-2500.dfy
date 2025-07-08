// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


module M {
  trait {:termination false} Top {
    predicate ActuallyTrue() ensures ActuallyTrue()
  }
  trait {:termination false} Tr extends Top {
    predicate True(): (ret: bool) ensures ret
    predicate True'() ensures True'()
    predicate ActuallyTrue'() ensures ActuallyTrue()
    predicate ActuallyTrue''() ensures var alsoThis := this; alsoThis.ActuallyTrue()
    predicate Other(x:nat, free: Tr)
      ensures x != 0 && free.Other(x-1, free) ==> Other(x-1, free)
  }
  method X(tr: Tr) requires tr.ActuallyTrue() {}
}

class Cl extends M.Tr {
  constructor() {}
  predicate True(): (ret: bool)
    // Missing: ensures ret
  { false }
  predicate True'()
    // Missing: ensures True'()
  { false }
  predicate ActuallyTrue()
    ensures ActuallyTrue()
  { true }
  predicate ActuallyTrue'()
    ensures ActuallyTrue()
  { true }
  predicate ActuallyTrue''()
     // This is logically correct. (Before CanCall, the disguised receiver in the Tr spec had prevented the override check from passing.)
     ensures ActuallyTrue''()
   { true }
  predicate Other(x: nat, free: M.Tr)
    // Different receiver
    ensures x != 0 && Other(x-1, free) ==> Other(x-1, free)
  { false }
}

method Meh(tr: M.Tr)
  requires tr.ActuallyTrue'()
{
  M.X(tr);
}

module SSCinClass {
  trait Trait {
    predicate Even(i: nat)
    predicate Odd(i: nat)
      ensures i == 0 || (i % 2 == 1) == Even(i-1)
  }

  class Class extends Trait {
    predicate Even(i: nat)
  { i == 0 || Odd(i-1) }
    predicate Odd(i: nat)
      ensures i == 0 || (i % 2 == 1) == Even(i-1)
    { i != 0 && Even(i-1) }
  }
}

module SSCinBoth {
  trait Trait {
    predicate Even(i: nat)
      ensures i == 0 || (i % 2 == 0) == Odd(i-1)
    predicate Odd(i: nat)
      ensures i == 0 || (i % 2 == 1) == Even(i-1)
  }

  class Class extends Trait {
    predicate Even(i: nat)
      ensures i == 0 || (i % 2 == 0) == Odd(i-1)
  { i == 0 || Odd(i-1) }
    predicate Odd(i: nat)
      ensures i == 0 || (i % 2 == 1) == Even(i-1)
    { i != 0 && Even(i-1) }
  }
}
