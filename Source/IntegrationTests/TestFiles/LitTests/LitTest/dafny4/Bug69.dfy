// RUN: %testDafnyForEachResolver "%s"


module M1
{
  ghost predicate X(i:int)
}

module M2
{
  import opened M1
  ghost predicate         P(i:int) requires X(i) { true } // ok
  predicate{:opaque} O(i:int) requires X(i) { true } // resolution/type error: X does not exist
}