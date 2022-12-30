// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module GiveT {
  type T = int
}

module Base {
  import opened GiveT

  function f(x : T):int { 0 }
}

module Refined refines Base {
  type T = int // OK -- local names take precedence over imported names

}

module ImportBase {
  import opened Base
}

module RefineImportBase refines ImportBase {
  import opened GiveT
}

module GiveT2 {
  type T = bool
}

module Refined2 refines GiveT {
  import opened GiveT2

  function f(x: T): int // OK: T is GiveT.T (refinement is preferred to import)
}

module GiveF{
  function {:opaque} f(): bool { true }
}

module BaseF{
  import opened GiveF

  lemma Test()
    ensures f() == true
  { reveal f(); }

}

module RefinedF refines BaseF {
  function f(): bool { false } // OK. Local f preferred over imported f
                               // even if imported into refinement parent

  lemma False()
    ensures false
  { reveal f(); Test(); }
}
