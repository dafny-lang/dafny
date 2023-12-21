// RUN: %exits-with 2 %dafny /typeSystemRefresh:1 /generalTraits:datatype /generalNewtypes:0 "%s" > "%t"
// RUN: %exits-with 2 %dafny /typeSystemRefresh:1 /generalTraits:datatype /generalNewtypes:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module VariousBaseTypes {
  newtype byteA = x | 0 <= x < 256

  newtype byteB = x: int | 0 <= x < 256

  newtype MyInt = int

  // cycle one way
  newtype A = B
  newtype B = c: C | true witness *
  newtype C = d | d < 100

  // cycle the other way
  newtype Z = d | d < 100
  newtype Y = c: Z | true witness *
  newtype X = Y

  newtype MyReal0 = real
  newtype MyReal1 = r | 0.0 <= r <= 100.0
  newtype MyReal2 = r: real | 0.0 <= r <= 100.0

  // The following are allowed with /generalNewtypes:1, but errors with /generalNewtypes:0

  newtype NotNumeric0 = bool // error: cannot base newtype on bool
  newtype NotNumeric1 = b | !b // error: cannot base newtype on bool
  newtype NotNumeric2 = b: bool | true // error: cannot base newtype on bool

  // The following are always errors

  newtype MyOrdinal = ORDINAL // error: cannot base newtype on ORDINAL

  trait Trait { }
  trait ReferenceTrait extends object { }
  class Cell { }

  newtype MyObject = object // error: cannot base newtype on (reference) trait
  newtype MyTrait = Trait // error: cannot base newtype on (non-reference) trait
  newtype MyReferenceTrait = ReferenceTrait // error: cannot base newtype on (reference) trait
  newtype MyCell? = Cell? // error: cannot base newtype on class
  newtype MyCell = Cell // error: cannot base newtype on class
}

module BaseTypesThatAreSubsetTypes {
  newtype byteB = x: nat | x < 256

  newtype MyNat = nat

  // cycle one way
  newtype A = B
  newtype B = c: C | true witness *
  newtype C = d: nat | d < 100

  // cycle the other way
  newtype Z = d: nat | d < 100
  newtype Y = c: Z | true witness *
  newtype X = Y

  type NonNegReal = r | 0.0 <= r
  newtype MyReal = NonNegReal
  newtype MyReal' = r: NonNegReal | r <= 100.0

  // The following are allowed with /generalNewtypes:1, but errors with /generalNewtypes:0

  type True = b | !!b
  newtype NotNumeric = True // error: cannot base newtype on bool
  newtype NotNumeric' = b: True | true // error: cannot base newtype on bool

  // The following are always errors

  type NonFiveOrdinal = o: ORDINAL | o != 5
  newtype MyOrdinal = NonFiveOrdinal // error: cannot base newtype on ORDINAL

  trait Trait { const n: int }
  type NonFiveTrait = t: Trait | t.n != 5
  trait ReferenceTrait extends object { const n: int }
  type NonFiveReferenceTrait = t: ReferenceTrait | t.n != 5
  class Cell { const n: int }
  type NonFiveCell? = t: Cell? | t == null || t.n != 5
  type NonFiveCell = t: Cell | t.n != 5

  newtype MyTrait = NonFiveTrait // error: cannot base newtype on (non-reference) trait
  newtype MyReferenceTrait = NonFiveReferenceTrait // error: cannot base newtype on (reference) trait
  newtype MyCell? = NonFiveCell? // error: cannot base newtype on class
  newtype MyCell = NonFiveCell // error: cannot base newtype on class
}

module SomeOperators {
  newtype TrueBool = b | b witness true
  newtype FalseBool = b | !b
  codatatype Stream = More(Stream)

  method Comparisons(x: TrueBool, y: FalseBool, z: bool, s: Stream, k: nat, o: ORDINAL) returns (r: TrueBool, r': FalseBool) {
    r := x == x;
    r := y == y;
    r := z == z;
    r := s ==#[k] s;
    r := s ==#[o] s;
    r := k == k;
    r := o == o;

    r := x <==> x;
    r := y <==> y; // error: <==> always results in the same type as its operands
    r := z <==> z; // error: <==> always results in the same type as its operands

    r := x ==> x;
    r := y ==> y; // error: ==> always results in the same type as its operands
    r := z ==> z; // error: ==> always results in the same type as its operands

    r := x <== x;
    r := y <== y; // error: <== always results in the same type as its operands
    r := z <== z; // error: <== always results in the same type as its operands

    r := x && x;
    r := y && y; // error: && always results in the same type as its operands
    r := z && z; // error: && always results in the same type as its operands

    r := x || x;
    r := y || y; // error: || always results in the same type as its operands
    r := z || z; // error: || always results in the same type as its operands

    r := k <= k;
    r := k >= k;
    r' := k < k;
    r' := k > k;
  }
}
