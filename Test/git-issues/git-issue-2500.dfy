// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  trait {:termination false} Tr {
    function True(): (ret: bool) ensures ret
    function True'(): (ret: bool) ensures True'()
    function Other(x:nat, free: Tr): bool
      ensures x != 0 && free.Other(x-1, free) ==> Other(x-1, free)
  }
}

class Class extends M.Tr {
  function True(): (ret: bool)
    // Missing: ensures ret != 0
  { false }
  function True'(): (ret: bool)
    // Missing: ensures True'()
  { false }
  function Other(x: nat, free: M.Tr): bool
    // Different Receiver
    ensures x != 0 && Other(x-1, free) ==> Other(x-1, free)
  { false }
}
