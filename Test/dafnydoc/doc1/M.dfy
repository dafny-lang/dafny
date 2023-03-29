/** Test module. More about this test module. */
module {:options "--function-syntax:4"} TestModule {

  const c: int := 7 + 
                    if true then 8 else 9*1 /** Number of items */
  const cc: real

  module MInner /** Hidden stuff */
  {}

  import opened MInner

  /** Opaque type */
  type T

  /** Enumeration */
  datatype D = A | B


  /** Returns a constant */
  function f(): int { 42 }

  method bump(i: int) returns (j: int) 
    // increments input
  {
    return i + 1;
  }

  class A {
    var j: int
    const c: int := 42
    method m(x: int)
      requires x > 0
      modifies this`j
      ensures j < 0
    {}
    predicate f<Q>() { true }
  }

  lemma IsX()
    requires true
    ensures true
}
