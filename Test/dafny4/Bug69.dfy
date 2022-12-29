// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1
{
  predicate X(i:int)
}

module M2
{
  import opened M1
  predicate          P(i:int) requires X(i) { true } // ok
  predicate{:opaque} O(i:int) requires X(i) { true } // resolution/type error: X does not exist
}
