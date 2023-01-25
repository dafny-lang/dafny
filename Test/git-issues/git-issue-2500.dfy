// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  trait {:termination false} Tr {
    function True(): (ret: bool) ensures ret
    function True'(): (ret: bool) ensures True'()
    function ActuallyTrue(): (ret: bool) ensures var alsoThis := this; alsoThis.ActuallyTrue()
    function Other(x:nat, free: Tr): bool
      ensures x != 0 && free.Other(x-1, free) ==> Other(x-1, free)
  }
}

class Class extends M.Tr {
  function True(): (ret: bool)
    // Missing: ensures ret
  { false }
  function True'(): (ret: bool)
    // Missing: ensures True'()
  { false }
  function ActuallyTrue(): (ret: bool)
    // This is logically correct, but the disguised receiver in the Tr spec prevents the override check from passing.
    ensures ActuallyTrue()
  { true }
  function Other(x: nat, free: M.Tr): bool
    // Different receiver
    ensures x != 0 && Other(x-1, free) ==> Other(x-1, free)
  { false }
}
