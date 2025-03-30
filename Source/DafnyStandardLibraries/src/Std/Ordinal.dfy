
module Std.Ordinal {

  // ghost predicate IsMinimal<T>(lessOrEqual: (T, T) -> bool, minimal: T, s: iset<T>) {
  //   minimal in s && forall x | x in s && lessOrEqual(x, minimal) :: lessOrEqual(minimal, x)
  // }

  // ghost predicate IsMaximal<T>(lessOrEqual: (T, T) -> bool, maximal: T, s: iset<T>) {
  //   maximal in s && forall x | x in s && lessOrEqual(maximal, x) :: lessOrEqual(x, maximal)
  // }

  ghost function {:axiom} Omega(): ORDINAL
    ensures !Omega().IsNat
    ensures Omega().IsLimit
    ensures forall other: ORDINAL | other.IsLimit && other != 0 :: Omega() <= other

  // TODO: Prove some of these via transfinite induction?

  // Additional axioms about addition

  lemma {:axiom} Succ(a: ORDINAL, b: ORDINAL)
    ensures a > b <==> a >= b + 1

  lemma SuccStrictlyIncreasing(a: ORDINAL, b: ORDINAL)
    requires a > b
    ensures a + 1 > b + 1
  {
    PlusDefinition(a, 1);
    PlusDefinition(b, 1);
  }

  ghost function {:axiom} PlusLimit(left: ORDINAL, right: ORDINAL): (result: ORDINAL)
    decreases right, 0
    ensures forall right' | right' < right :: Plus(left, right') < result
    ensures forall result' | 
      forall right' | right' < right :: Plus(left, right') < result :: result <= result'

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

  lemma PlusAndIsLimit(left: ORDINAL, right: ORDINAL)
    requires right.IsLimit
    ensures (left + right).IsLimit
  {
    PlusDefinition(left, right);
  }

  @ResourceLimit("0")
  @IsolateAssertions
  lemma PlusStrictlyIncreasingOnRight(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    requires right > right'
    decreases right
    ensures left + right > left + right'
  {
    PlusDefinition(left, right);
    PlusDefinition(left, right');
    if right == 0 {
    } else if right.IsLimit {
      var x :| right > x > right';
      PlusDefinition(left, x);
      PlusStrictlyIncreasingOnRight(left, x, right');
    } else {
      if right' == right - 1 {
      } else {
        if right' > right - 1 {
          Succ(right', right - 1);
          assert false;
        }
        assert right - 1 > right';
        PlusStrictlyIncreasingOnRight(left, right - 1, right');
        assert left + (right - 1) > left + right';
        assert (left + (right - 1)) + 1 > left + right';
        SuccAndPlus(left, right - 1);
        assert (left + ((right - 1) + 1)) > left + right';
        assert left + right > left + right';
      }
    }
    
  }

  lemma PlusIncreasingOnLeft(left: ORDINAL, left': ORDINAL, right: ORDINAL)
    requires left >= left'
    decreases right
    ensures left + right >= left' + right
  {
    PlusDefinition(left, right);
    PlusDefinition(left', right);
    if right == 0 {
    } else if right.IsLimit {
    } else {
      PlusIncreasingOnLeft(left, left', right - 1);
      if left + (right - 1) == left' + (right - 1) {
        assert left + (right - 1) == left' + (right - 1);
        assert (left + (right - 1)) + 1 == (left' + (right - 1)) + 1;
        SuccAndPlus(left, right - 1);
        SuccAndPlus(left', right - 1);
      } else {
        assert left + (right - 1) > left' + (right - 1);
        SuccStrictlyIncreasing(left + (right - 1), left' + (right - 1));
        assert (left + (right - 1)) + 1 > (left' + (right - 1)) + 1;
        SuccAndPlus(left, right - 1);
        SuccAndPlus(left', right - 1);
      }
    }
  }

  lemma SuccAndPlus(left: ORDINAL, right: ORDINAL)
    decreases right
    ensures (left + right) + 1 == left + (right + 1)
  {
    PlusDefinition(left, right + 1);
    PlusDefinition(left, right);
  }

  @ResourceLimit("0")
  @IsolateAssertions
  lemma PlusIsAssociative(x: ORDINAL, y: ORDINAL, z: ORDINAL)
    decreases z
    ensures (x + y) + z == x + (y + z)
  {
    if z == 0 {
    } else if z.IsLimit {
      PlusAndIsLimit(y, z);
      assert (y + z).IsLimit;
      // assume false;
    } else {
      calc {
        (x + y) + z;
        (x + y) + ((z - 1) + 1);
        { SuccAndPlus(x + y, z - 1); }
        ((x + y) + (z - 1)) + 1;
        { PlusIsAssociative(x, y, z - 1); }
        (x + (y + (z - 1))) + 1;
        { SuccAndPlus(x, y + (z - 1)); }
        x + ((y + (z - 1)) + 1);
        { SuccAndPlus(y, z - 1); }
        x + (y + ((z - 1) + 1));
        x + (y + z);
      }
    }
  }

  // Multiplication and axioms about multiplication

  ghost function {:axiom} TimesLimit(left: ORDINAL, right: ORDINAL): (result: ORDINAL)
    decreases right, 0
    ensures forall right' | right' < right :: Times(left, right') < result
    ensures forall result' | forall right' | right' < right :: Times(left, right') < result :: result <= result'

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

  @ResourceLimit("0")
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
    requires left > 0
    requires right > right'
    ensures Times(left, right) > Times(left, right')

  lemma {:axiom} TimesIncreasingOnLeft(left: ORDINAL, left': ORDINAL, right: ORDINAL)
    requires left >= left'
    ensures Times(left, right) > Times(left', right)
  {
    if right.IsLimit {
      forall right' | right' < right {
        TimesIncreasingOnLeft(left, left', right');
      }
    } else {
      TimesIncreasingOnLeft(left, left', right - 1);
    }
  }

  @ResourceLimit("1e9")
  lemma TimesDistributesOnLeft(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    decreases right'
    ensures Times(left, right + right') == Times(left, right) + Times(left, right')
  {
    if right' == 0 {
    } else if right'.IsLimit {
      PlusDefinition(right, right');
      assert (right + right').IsLimit;
      calc {
        Times(left, right + right');
        TimesLimit(left, right + right');
      }
    } else {
      calc {
        Times(left, right + right');
        Times(left, right + ((right' - 1) + 1));
        { PlusIsAssociative(right, right' - 1, 1); }
        Times(left, (right + (right' - 1)) + 1);
        Times(left, right + (right' - 1)) + left;
        { TimesDistributesOnLeft(left, right, right' - 1); }
        Times(left, right) + Times(left, right' - 1) + left;
        { PlusIsAssociative(Times(left, right), Times(left, right' - 1), left); }
        Times(left, right) + (Times(left, right' - 1) + left);
        Times(left, right) + Times(left, right');
      }
    }
  }

  // Helpful lemmas and utilities

  /** Maximum of two ordinals  */
  function Max(a: ORDINAL, b: ORDINAL): ORDINAL
  {
    if a < b
    then b
    else a
  }

  lemma MaxIsAssociative(a: ORDINAL, b: ORDINAL, c: ORDINAL)
    ensures Max(Max(a, b), c) == Max(a, Max(b, c))
  {}

  lemma RadixDecreases(base: ORDINAL, a: ORDINAL, a': ORDINAL, b: ORDINAL)
    requires base > b
    requires a > a'
    ensures Times(base, a) > Times(base, a') + b
  {
    Succ(a, a');
    assert a >= a' + 1;

    TimesDistributesOnLeft(base, a', 1);
    assert Times(base, a' + 1) == Times(base, a') + Times(base, 1);
    TimesLeftIdentity(base);
    assert Times(base, a' + 1) == Times(base, a') + base;

    if a == a' + 1 {
      calc {
        Times(base, a);
        Times(base, a' + 1);
        Times(base, a') + base;
      > { PlusStrictlyIncreasingOnRight(Times(base, a'), base, b); }
        Times(base, a') + b;
      }
    } else {
      calc {
        Times(base, a);
      >= { TimesStrictlyIncreasingOnRight(base, a, a' + 1); }
        Times(base, a' + 1);
        Times(base, a') + base;
      > { PlusStrictlyIncreasingOnRight(Times(base, a'), base, b); }
        Times(base, a') + b;
      }
    }
  }
}