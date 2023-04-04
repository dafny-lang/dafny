/** Test module. More about this test module. */
module {:options "--function-syntax:4"} TestModule {

  const c: int := 7 + 
                    if true then 8 else 9*1 /** Number of items. ALl of them. */

  const {:myattribute} cc: real
  // The distance.
  const ccc: bool
  /** Valid or not. */
  const {:myattribute}{:otherattribute 5,6} cccc: A?
    // The internal state.

  module MInner /** Hidden stuff */
  {}

  import opened MInner

  /** Opaque type */
  type T

  /** Enumeration. Various options. */
  datatype D = A | B


  /** Returns a constant. A special constant. */
  function f(): int { 42 }

  function fif(): int 
    // return a constant. A special constant.
  { 42 }

  twostate function tf(): int 
    /** A two-state function */
  { 42 }

  predicate p() 
    // Always true. Every time.
    ensures p() == true
  { true }

  predicate pp() 
    /** Always true. Every time. */
    ensures p() == true
  { true }

  predicate ppp() 
    // Always true. Every time.
  { true }

  least predicate lp() /** A copredicate */ { false }

  method bump(i: int) returns (j: int) 
    // increments input
  {
    return i + 1;
  }

  /** Sets to zero. Absolute zero. */
  ghost method {:iszero} zero() returns (z: int) 
    ensures z == 0
  {
    return 0;
  }

  class A 
   // Holds all the state. Every bit.
  {
    var j: int // level
    var k: D // options
    const c: int := 42
    method m(x: int)
      requires x > 0
      modifies this`j
      ensures j < 0
    {}
    predicate f<Q>() { true }
  }

  lemma {:myattribute} IsX()
    // always true
    requires true
    ensures true

  twostate lemma TS()
    requires true
    ensures true
}
