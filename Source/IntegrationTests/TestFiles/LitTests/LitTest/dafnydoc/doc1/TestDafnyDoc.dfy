// RUN: %baredafny doc --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%S"/docs-expected/index.html ./docs/index.html 
// RUN: %diff "%S"/docs-expected/TestModule_214638566.html ./docs/TestModule_214638566.html 

/** Test module. More about this test module. */
module {:options "--function-syntax:4"} TestModule {

  const c := 7 +
             if true then 8 else 9*1 /** Number of items. All of them. */

  const {:myattribute} cc: real // The distance.
  const ccc: bool // Valid or not.
  const {:myattribute}{:otherattribute 5,6} cccc: A? // The internal state.

  const f1: int -> int
  const f2: set<int> ~> seq<int>
  const f3: bool --> TQ<int>
  const tup0: ()
  const tup2: (B?<real>, set<int>) := (null, {})

  module MInner /** Hidden stuff */
  {
    export // something
      reveals p  provides MII
    export E1 /** two things */
      provides icc
      reveals ic
    export E2 /** everything */ reveals *

    /** An extending example */
    export E3 extends E1, MInner reveals f

    const ic := 0
    const icc := 1
    predicate p() { true }
    function f(): int { 42 - 6*7 }
    module MII { export Nothing }
  }

  import opened MInner
  import     opened J = MInner`E1
  import L = MInner`E2

  /** A very abstract type. 100% dark. */
  type T  { method m() /* Special method. */ {} }
  type TQ<Y>

  /** Enumeration. Various options. */
  datatype D<Q> = A(q: Q) | B {}

  codatatype CD<Q> =
    | Y // A Y
    | Z /* A Z, with a very long description so that it overflows a line to check that line wrapping happens sensibly for data type constructors, which are laid out in table cells.  */
    | ghost G // A ghost constructor. Very cool.

  /** A type synonym. */
  type Tint(==) = B<int>

  type TTT<!Q(0)> = B<Q>

  type WW(==,0,!new,00)

  /** A small subset type */
  type Small = x: nat | x < 100
  type SmallW(==) = x: nat | x < 100 witness 99
  type SmallS = x: nat | x < 100 witness *

  /** A brand new type */
  newtype {:native "uint8"} Smaller = x: nat | x < 10 witness 9

  newtype Dup = int { predicate IsEven() { this %2 == 0 } }

  newtype Size = x | 0 <= x < 1000

  /** Returns a constant. A special constant. */
  function f(r: real, x: int := 0): int
    ensures f(r,x) == 42
  { 42 }

  opaque predicate pp(older a: A?, ghost nameonly x: int ) { true }

  function fif(nameonly z: A): A?
    // return a constant. A special constant.
  { null }

  twostate function tf(a: A, new b: A): int
    /** A two-state function */
  { 42  // some comment
    -
    6 /* another comment */ *
    7 // the final comment
  }

  predicate p()
    // Always true. Every time.
    ensures p() == true
  { true }

  predicate pf()
    /** Always true. Every time. */
    ensures pp(null, x := 1) == true
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

  method ModifyA(a: A)
    modifies a, a`j
  {}

  /** Sets to zero. Absolute zero. */
  ghost method {:iszero} zero() returns (z: int)
    ensures z == 0
  {
    return 0;
  }

  iterator Gen(start: int) yields (x: int)
    yield ensures |xs| <= 10 && x == start + |xs| - 1
  {
    var i := 0;
    while i < 10 invariant |xs| == i {
      x := start + i;
      yield;
      i := i + 1;
    }
  }

  class A extends T2
    // Holds all the state. Every bit.
  {
    var j: int // level
    ghost var k: D<int> // options
    const {:opaque} c: int := 42 // The meaning of life.
    method m(x: int)
      requires x > 0
      modifies this, this`j
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

  datatype BB<*Q> = R(q: Q)

  lemma {:myattribute} IsX()
    // always true
    requires true
    ensures true

  twostate lemma TS()
    requires true
    ensures true


  trait T1<TR> extends object, T3 /** A special trait */ {
    const one := 1
    var count: int
  }
  trait T2 extends T1<A>, T3 {}
  trait T3 {
    predicate ftr()
    predicate ftz() { true }
    method mmm() {}
  }

  abstract module P {
    method P1() {}
    method P2()
  }
  module Q refines P {
    method Q1() {}
  }
  abstract module S {
    import Z: P
    method ss() {}
  }
}



const ctop := 131
