// RUN: %baredafny doc --use-basename-for-filename "%s" > "%t"

/** Test module. More about this test module. */
module {:options "--function-syntax:4"} TestModule {

  const c := 7 + 
                    if true then 8 else 9*1 /** Number of items. All of them. */

  const {:myattribute} cc: real
  // The distance.
  const ccc: bool
  /** Valid or not. */
  const {:myattribute}{:otherattribute 5,6} cccc: A?
    // The internal state.

  module MInner /** Hidden stuff */
  {
    export // something
      reveals p  provides MII
    export E1 reveals ic /** one thing */
    export E2 /** everything */ reveals *

    /** An extending example */
    export E3 extends E1, MInner reveals f

    const ic := 0
    predicate p() { true }
    function f(): int { 42 }
    module MII { export Nothing }
  }

  import opened J = MInner
  import     opened MInner`E1
  import L = MInner`E2

  /** Opaque type */
  type T  {}
  type TQ<Y>

  /** Enumeration. Various options. */
  datatype D<Q> = A(q: Q) | B {}


  /** Type synonym. */
  type Tint = B<int>

  type TTT<Q(0)> = B<Q>

  /** Subset type */
  type Small = x: nat | x < 100

  /** New type */
  newtype {:native "uint8"} Smaller = x: nat | x < 10

  newtype Dup = int {}

  newtype Size = x | 0 <= x < 1000

  /** Returns a constant. A special constant. */
  function f(r: real, ghost x: int): int 
    ensures f(r,x) == 42
  { 42 }

  function fif(nameonly z: A): A? 
    // return a constant. A special constant.
  { null }

  twostate function tf(): int 
    /** A two-state function */
  { 42 }

  predicate p() 
    // Always true. Every time.
    ensures p() == true
  { true }

  predicate pp() 
    /** Always true. Every time. */
    ensures pp() == true
  { true }

  predicate ppp(s: seq<int>, ss: set<A?>, mm: map<set<A>,seq<set<A?>>>) 
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

  class A extends T2
   // Holds all the state. Every bit.
  {
    var j: int // level
    ghost var k: D<int> // options
    const {:opaque} c: int := 42 // The meaning of life.
    method m(x: int)
      requires x > 0
      modifies this`j
      ensures 0 < 1
    {}
    predicate f<Q>() { true }
    predicate ftr() /** Implements T3.ftr */ { true }

    constructor ()
      // default constructor
    {}
    constructor A(i: int)
      // Non-default constructor
    {}
  }

  class B<Z(0)> extends T2 {
    var j: Z
    predicate ftr() /** Implements T3.ftr */ { true }
  }

  lemma {:myattribute} IsX()
    // always true
    requires true
    ensures true

  twostate lemma TS()
    requires true
    ensures true


  trait T1<TR> extends T3 {}
  trait T2 extends T1<A>, T3 {}
  trait T3 {
    predicate ftr()
  }
}


const ctop := 131
