// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
}

class Cl extends M.Tr {
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
     // This is logically correct, but the disguised receiver in the Tr spec prevents the override check from passing.
     ensures ActuallyTrue''()
   { true }
  predicate Other(x: nat, free: M.Tr)
    // Different receiver
    ensures x != 0 && Other(x-1, free) ==> Other(x-1, free)
  { false }
}

module SSCinClass {
  trait Trait {
    predicate Even(i: nat)
    predicate Odd(i: nat)
      ensures if i == 0 then true else (i % 2 == 1) == Even(i-1)
  }

  class Class extends Trait {
    predicate Even(i: nat)
  { if i == 0 then true else Odd(i-1) }
    predicate Odd(i: nat)
      ensures if i == 0 then true else (i % 2 == 1) == Even(i-1)
    { if i == 0 then false else Even(i-1) }
  }
}

module SSCinBoth {
  trait Trait {
    predicate Even(i: nat)
      ensures if i == 0 then true else (i % 2 == 0) == Odd(i-1)
    predicate Odd(i: nat)
      ensures if i == 0 then true else (i % 2 == 1) == Even(i-1)
  }

  class Class extends Trait {
    predicate Even(i: nat)
      ensures if i == 0 then true else (i % 2 == 0) == Odd(i-1)
  { if i == 0 then true else Odd(i-1) }
    predicate Odd(i: nat)
      ensures if i == 0 then true else (i % 2 == 1) == Even(i-1)
    { if i == 0 then false else Even(i-1) }
  }
}
