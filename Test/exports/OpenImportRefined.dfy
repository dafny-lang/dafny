// RUN: %dafny /env:0 /dprint:"%t.dfy" /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module GiveT {
  type T = int
}

module Base {
  import opened GiveT

  function f(x : T):int { 0 }
}

module Refined refines Base {
  type T = int //causes error, can't define a T given that it's imported as opened

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

  function f(x: T): int //error, which T?
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
  function f(): bool { false } // error

  lemma False()
    ensures false
  { reveal f(); Test(); }
}
