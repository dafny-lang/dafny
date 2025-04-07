/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Ordinal {

  ghost function {:axiom} Omega(): ORDINAL
    ensures !Omega().IsNat
    ensures Omega().IsLimit
    ensures forall other: ORDINAL | other.IsLimit && other != 0 :: Omega() <= other

  // Additional axioms about addition

  lemma {:axiom} Succ(a: ORDINAL, b: ORDINAL)
    ensures a < b <==> a + 1 <= b

  ghost function {:axiom} PlusLimit(left: ORDINAL, right: ORDINAL): (result: ORDINAL)
    ensures forall right' | right' < right :: Plus(left, right') < result
    ensures forall result' {:trigger} |
              forall right' | right' < right :: Plus(left, right') < result' :: result <= result'
    decreases right, 0

  ghost function Plus(left: ORDINAL, right: ORDINAL): ORDINAL
    decreases right
  {
    if right == 0 then
      0
    else if right.IsLimit then
      PlusLimit(left, right)
    else
      Plus(left, right - 1) + 1
  }

  lemma {:axiom} PlusDefinition(left: ORDINAL, right: ORDINAL)
    ensures Plus(left, right) == left + right

  lemma {:axiom} PlusStrictlyIncreasingOnRight(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    requires right < right'
    ensures left + right < left + right'
    decreases right

  lemma {:axiom} PlusIncreasingOnLeft(left: ORDINAL, left': ORDINAL, right: ORDINAL)
    requires left <= left'
    ensures left + right <= left' + right

  lemma SuccStrictlyIncreasing(a: ORDINAL, b: ORDINAL)
    requires a < b
    ensures a + 1 < b + 1
  {
    PlusDefinition(a, 1);
    PlusDefinition(b, 1);
  }

  lemma SuccIncreasing(a: ORDINAL, b: ORDINAL)
    requires a <= b
    ensures a + 1 <= b + 1
  {
    PlusDefinition(a, 1);
    PlusDefinition(b, 1);
  }

  lemma {:axiom} PlusIsAssociative(x: ORDINAL, y: ORDINAL, z: ORDINAL)
    decreases z
    ensures (x + y) + z == x + (y + z)

  // Multiplication and axioms about multiplication

  ghost function {:axiom} TimesLimit(left: ORDINAL, right: ORDINAL): (result: ORDINAL)
    ensures forall right' | right' < right :: Times(left, right') < result
    ensures forall result' {:trigger} | (forall right' | right' < right :: Times(left, right') < result') :: result <= result'
    decreases right, 0

  ghost function Times(left: ORDINAL, right: ORDINAL): (result: ORDINAL)
    decreases right
  {
    if right == 0 then
      0
    else if right.IsLimit then
      TimesLimit(left, right)
    else
      Times(left, right - 1) + left
  }

  lemma TimesLeftIdentity(o: ORDINAL)
    ensures Times(1, o) == o
  {
    if o.IsLimit {
      assert Times(1, o) <= o;
    } else {
      TimesLeftIdentity(o - 1);
    }
  }

  lemma TimesRightIdentity(o: ORDINAL)
    ensures Times(o, 1) == o
  {}

  lemma {:axiom} TimesStrictlyIncreasingOnRight(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    requires 0 < left
    requires right < right'
    ensures Times(left, right) < Times(left, right')

  lemma {:axiom} TimesIncreasingOnLeft(left: ORDINAL, left': ORDINAL, right: ORDINAL)
    requires left <= left'
    ensures Times(left, right) < Times(left', right)

  lemma {:axiom} TimesDistributesOnLeft(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    ensures Times(left, right + right') == Times(left, right) + Times(left, right')
    decreases right'

  // Helpful lemmas and utilities

  /** Maximum of two ordinals  */
  function Max(a: ORDINAL, b: ORDINAL): ORDINAL
  {
    if a < b
    then b
    else a
  }

  lemma RadixStrictlyIncreasing(base: ORDINAL, a: ORDINAL, a': ORDINAL, b: ORDINAL)
    requires a < a'
    requires b < base
    ensures Times(base, a) + b < Times(base, a')
  {
    Succ(a, a');
    assert a + 1 <= a';

    TimesDistributesOnLeft(base, a', 1);
    assert Times(base, a' + 1) == Times(base, a') + Times(base, 1);
    TimesLeftIdentity(base);
    assert Times(base, a' + 1) == Times(base, a') + base;

    if a + 1 == a' {
      calc {
        Times(base, a) + b;
      < { PlusStrictlyIncreasingOnRight(Times(base, a), b, base); }
        Times(base, a) + base;
        Times(base, a + 1);
        Times(base, a');
      }
    } else {
      calc {
        Times(base, a) + b;
      < { PlusStrictlyIncreasingOnRight(Times(base, a), b, base); }
        Times(base, a) + base;
        Times(base, a + 1);
      <= { TimesStrictlyIncreasingOnRight(base, a + 1, a'); }
        Times(base, a');
      }
    }
  }
}