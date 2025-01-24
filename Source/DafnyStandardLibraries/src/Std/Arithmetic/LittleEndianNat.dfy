/*******************************************************************************
 *  Original: Copyright (c) 2020 Secure Foundations Lab
 *  SPDX-License-Identifier: MIT
 *  
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
Little endian interpretation of a sequence of numbers with a given base. The
first element of a sequence is the least significant position; the last
element is the most significant position.
 */
@DisableNonlinearArithmetic
abstract module Std.Arithmetic.LittleEndianNat {

  import opened DivMod
  import opened Mul
  import opened Power
  import opened Collections.Seq
  import opened Logarithm

  function BASE(): nat
    ensures BASE() > 1

  type digit = i: nat | 0 <= i < BASE()

  //////////////////////////////////////////////////////////////////////////////
  //
  // ToNat definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a sequence to a nat beginning with the least significant position. */
  function ToNatRight(xs: seq<digit>): nat
  {
    if |xs| == 0 then 0
    else
      LemmaMulNonnegativeAuto();
      ToNatRight(DropFirst(xs)) * BASE() + First(xs)
  }

  /* Converts a sequence to a nat beginning with the most significant position. */
  function ToNatLeft(xs: seq<digit>): nat
  {
    if |xs| == 0 then 0
    else
      LemmaPowPositiveAuto();
      LemmaMulNonnegativeAuto();
      ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1)
  }

  /* Given the same sequence, ToNatRight and ToNatLeft return the same nat. */
  @IsolateAssertions
  lemma LemmaToNatLeftEqToNatRight(xs: seq<digit>)
    ensures ToNatRight(xs) == ToNatLeft(xs)
  {
    if xs == [] {
    } else {
      if DropLast(xs) == [] {
        calc {
          ToNatLeft(xs);
          Last(xs) * Pow(BASE(), |xs| - 1);
          {  }
          Last(xs);
          First(xs);
          { assert ToNatRight(DropFirst(xs)) == 0; }
          ToNatRight(xs);
        }
      } else {
        calc {
          ToNatLeft(xs);
          ToNatLeft(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
          { LemmaToNatLeftEqToNatRight(DropLast(xs)); }
          ToNatRight(DropLast(xs)) + Last(xs) * Pow(BASE(), |xs| - 1);
          ToNatRight(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs)
          * Pow(BASE(), |xs| - 1);
          { LemmaToNatLeftEqToNatRight(DropFirst(DropLast(xs))); }
          ToNatLeft(DropFirst(DropLast(xs))) * BASE() + First(xs) + Last(xs)
          * Pow(BASE(), |xs| - 1);
          {
            assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
            LemmaMulProperties();
          }
          ToNatLeft(DropLast(DropFirst(xs))) * BASE() + First(xs) + Last(xs)
          * Pow(BASE(), |xs| - 2) * BASE();
          { LemmaMulIsDistributiveAddOtherWayAuto(); }
          ToNatLeft(DropFirst(xs)) * BASE() + First(xs);
          { LemmaToNatLeftEqToNatRight(DropFirst(xs)); }
          ToNatRight(xs);
        }
      }
    }
  }

  lemma LemmaToNatLeftEqToNatRightAuto()
    ensures forall xs: seq<digit> :: ToNatRight(xs) == ToNatLeft(xs)
  {
    forall xs: seq<digit>
      ensures ToNatRight(xs) == ToNatLeft(xs)
    {
      LemmaToNatLeftEqToNatRight(xs);
    }
  }

  /* The nat representation of a sequence of length 1 is its first (and only)
  position. */
  lemma LemmaSeqLen1(xs: seq<digit>)
    requires |xs| == 1
    ensures ToNatRight(xs) == First(xs)
  {
    assert ToNatRight(DropFirst(xs)) == 0;
  }

  /* The nat representation of a sequence of length 2 is sum of its first
  position and the product of its second position and BASE(). */
  lemma LemmaSeqLen2(xs: seq<digit>)
    requires |xs| == 2
    ensures ToNatRight(xs) == First(xs) + xs[1] * BASE()
  {
    var xs1 := DropFirst(xs);
    calc {
      ToNatRight(xs);
      ToNatRight(xs1) * BASE() + First(xs);
      (ToNatRight([]) * BASE() + First(xs1)) * BASE() + First(xs);
      (0 * BASE() + First(xs1)) * BASE() + First(xs);
    }
  }

  /* Appending a zero does not change the nat representation of the sequence. */
  lemma LemmaSeqAppendZero(xs: seq<digit>)
    ensures ToNatRight(xs + [0]) == ToNatRight(xs)
  {
    LemmaToNatLeftEqToNatRightAuto();
    calc {
      ToNatRight(xs + [0]);
      ToNatLeft(xs + [0]);
      ToNatLeft(xs) + 0 * Pow(BASE(), |xs|);
      { LemmaMulBasicsAuto(); }
      ToNatLeft(xs);
      ToNatRight(xs);
    }
  }

  /* The nat representation of a sequence is bounded by BASE() to the power of
  the sequence length. */
  lemma LemmaSeqNatBound(xs: seq<digit>)
    ensures ToNatRight(xs) < Pow(BASE(), |xs|)
  {
    if |xs| == 0 {
    } else {
      var len' := |xs| - 1;
      var pow := Pow(BASE(), len');
      calc {
        ToNatRight(xs);
         { LemmaToNatLeftEqToNatRight(xs); }
        ToNatLeft(xs);
         {  }
        ToNatLeft(DropLast(xs)) + Last(xs) * pow;
      <  {
           LemmaToNatLeftEqToNatRight(DropLast(xs));
           LemmaSeqNatBound(DropLast(xs));
         }
        pow + Last(xs) * pow;
      <= {
           LemmaPowPositiveAuto();
           LemmaMulInequalityAuto();
         }
        pow + (BASE() - 1) * pow;
         { LemmaMulIsDistributiveAuto(); }
        Pow(BASE(), len' + 1);
      }
    }
  }

  /* The nat representation of a sequence can be calculated using the nat
  representation of its prefix. */
  @IsolateAssertions
  lemma LemmaSeqPrefix(xs: seq<digit>, i: nat)
    requires 0 <= i <= |xs|
    ensures ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i) == ToNatRight(xs)
  {
    if i == 1 {
      assert ToNatRight(xs[..1]) == First(xs);
    } else if i > 1 {
      calc {
        ToNatRight(xs[..i]) + ToNatRight(xs[i..]) * Pow(BASE(), i);
        ToNatRight(DropFirst(xs[..i])) * BASE() + First(xs) + ToNatRight(xs[i..]) * Pow(BASE(), i);
        {
          assert DropFirst(xs[..i]) == DropFirst(xs)[..i-1];
          LemmaMulProperties();
        }
        ToNatRight(DropFirst(xs)[..i-1]) * BASE() + First(xs) + (ToNatRight(xs[i..]) * Pow(BASE(), i - 1)) * BASE();
        { LemmaMulIsDistributiveAddOtherWayAuto(); }
        (ToNatRight(DropFirst(xs)[..i-1]) + ToNatRight(DropFirst(xs)[i-1..]) * Pow(BASE(), i - 1)) * BASE() + First(xs);
        { LemmaSeqPrefix(DropFirst(xs), i - 1); }
        ToNatRight(xs);
      }
    }
  }

  /* If there is an inequality between the most significant positions of two
  sequences, then there is an inequality between the nat representations of
  those sequences. Helper lemma for LemmaSeqNeq. */
  lemma LemmaSeqMswInequality(xs: seq<digit>, ys: seq<digit>)
    requires |xs| == |ys| > 0
    requires Last(xs) < Last(ys)
    ensures ToNatRight(xs) < ToNatRight(ys)
  {
    LemmaToNatLeftEqToNatRightAuto();
    var len' := |xs| - 1;
    calc {
      ToNatRight(xs);
      ToNatLeft(xs);
    <  { LemmaSeqNatBound(DropLast(xs)); }
      Pow(BASE(), len') + Last(xs) * Pow(BASE(), len');
    == { LemmaMulIsDistributiveAuto(); }
      (1 + Last(xs)) * Pow(BASE(), len');
    <= { LemmaPowPositiveAuto(); LemmaMulInequalityAuto(); }
      ToNatLeft(ys);
      ToNatRight(ys);
    }
  }

  /* Two sequences do not have the same nat representations if their prefixes
  do not have the same nat representations. Helper lemma for LemmaSeqNeq. */
  @IsolateAssertions
  lemma LemmaSeqPrefixNeq(xs: seq<digit>, ys: seq<digit>, i: nat)
    requires 0 <= i <= |xs| == |ys|
    requires ToNatRight(xs[..i]) != ToNatRight(ys[..i])
    ensures ToNatRight(xs) != ToNatRight(ys)
    decreases |xs| - i
  {
    if i == |xs| {
      assert xs[..i] == xs;
      assert ys[..i] == ys;
    } else {
      if xs[i] == ys[i] {
        assert DropLast(xs[..i+1]) == xs[..i];
        assert DropLast(ys[..i+1]) == ys[..i];

        LemmaToNatLeftEqToNatRightAuto();
        assert ToNatRight(xs[..i+1]) == ToNatLeft(xs[..i+1]);
      } else if xs[i] < ys[i] {
        LemmaSeqMswInequality(xs[..i+1], ys[..i+1]);
      } else {
        LemmaSeqMswInequality(ys[..i+1], xs[..i+1]);
      }
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }
  }

  /* If two sequences of the same length are not equal, their nat
  representations are not equal. */
  lemma LemmaSeqNeq(xs: seq<digit>, ys: seq<digit>)
    requires |xs| == |ys|
    requires xs != ys
    ensures ToNatRight(xs) != ToNatRight(ys)
  {
    ghost var i: nat, n: nat := 0, |xs|;

    while i < n
      invariant 0 <= i < n
      invariant xs[..i] == ys[..i]
    {
      if xs[i] != ys[i] {
        break;
      }
      i := i + 1;
    }
    assert ToNatLeft(xs[..i]) == ToNatLeft(ys[..i]);

    assert xs[..i+1][..i] == xs[..i];
    assert ys[..i+1][..i] == ys[..i];
    LemmaPowPositiveAuto();
    LemmaMulStrictInequalityAuto();
    assert ToNatLeft(xs[..i+1]) != ToNatLeft(ys[..i+1]);
    LemmaToNatLeftEqToNatRightAuto();

    LemmaSeqPrefixNeq(xs, ys, i+1);
  }

  /* If the nat representations of two sequences of the same length are equal
  to each other, the sequences are the same. */
  lemma LemmaSeqEq(xs: seq<digit>, ys: seq<digit>)
    requires |xs| == |ys|
    requires ToNatRight(xs) == ToNatRight(ys)
    ensures xs == ys
  {
    calc ==> {
      xs != ys;
      { LemmaSeqNeq(xs, ys); }
      ToNatRight(xs) != ToNatRight(ys);
      false;
    }
  }

  /* The nat representation of a sequence and its least significant position are
  congruent. */
  @IsolateAssertions
  lemma LemmaSeqLswModEquivalence(xs: seq<digit>)
    requires |xs| >= 1
    ensures IsModEquivalent(ToNatRight(xs), First(xs), BASE())
  {
    if |xs| == 1 {
      LemmaSeqLen1(xs);
      LemmaModEquivalenceAuto();
    } else {
      assert IsModEquivalent(ToNatRight(xs), First(xs), BASE()) by {
        calc ==> {
          true;
          { LemmaModEquivalence(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE()); }
          IsModEquivalent(ToNatRight(xs), ToNatRight(DropFirst(xs)) * BASE() + First(xs), BASE());
          { LemmaModMultiplesBasicAuto(); }
          IsModEquivalent(ToNatRight(xs), First(xs), BASE());
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // FromNat definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a nat to a sequence. */
  function FromNat(n: nat): (xs: seq<digit>)
  {
    if n == 0 then []
    else
      LemmaDivBasicsAuto();
      LemmaDivDecreasesAuto();
      [n % BASE()] + FromNat(n / BASE())
  }

  lemma LemmaFromNatLen2(n: nat)
    ensures n == 0 ==> |FromNat(n)| == 0
    ensures n > 0 ==> |FromNat(n)| == Log(BASE(), n) + 1
  {
    var digits := FromNat(n);
    if (n == 0) {
    } else {
      assert |digits| == Log(BASE(), n) + 1 by {
        LemmaDivBasicsAuto();
        var digits' := FromNat(n / BASE());
        assert |digits| == |digits'| + 1;
        if n < BASE() {
          LemmaLog0(BASE(), n);
          assert n / BASE() == 0 by { LemmaBasicDiv(BASE()); }
        } else {
          LemmaLogS(BASE(), n);
          assert n / BASE() > 0 by { LemmaDivNonZeroAuto(); }
        }
      }
    }
  }

  /* Ensures length of the sequence generated by FromNat is less than len.
  Helper lemma for FromNatWithLen. */
  lemma LemmaFromNatLen(n: nat, len: nat)
    requires Pow(BASE(), len) > n
    ensures |FromNat(n)| <= len
  {
    if n == 0 {
    } else {
      calc {
        |FromNat(n)|;
      == { LemmaDivBasicsAuto(); }
        1 + |FromNat(n / BASE())|;
      <= {
           LemmaMultiplyDivideLtAuto();
           LemmaDivDecreasesAuto();
           LemmaFromNatLen(n / BASE(), len - 1);
         }
        len;
      }
    }
  }

  /* If we start with a nat, convert it to a sequence, and convert it back, we
  get the same nat we started with. */
  lemma LemmaNatSeqNat(n: nat)
    ensures ToNatRight(FromNat(n)) == n
    decreases n
  {
    if n == 0 {
    } else {
      calc {
        ToNatRight(FromNat(n));
        { LemmaDivBasicsAuto(); }
        ToNatRight([n % BASE()] + FromNat(n / BASE()));
        n % BASE() + ToNatRight(FromNat(n / BASE())) * BASE();
        {
          LemmaDivDecreasesAuto();
          LemmaNatSeqNat(n / BASE());
        }
        n % BASE() + n / BASE() * BASE();
        { LemmaFundamentalDivMod(n, BASE()); }
        n;
      }
    }
  }

  /* Extends a sequence to a specified length. */
  opaque function SeqExtend(xs: seq<digit>, n: nat): (ys: seq<digit>)
    requires |xs| <= n
    ensures |ys| == n
    ensures ToNatRight(ys) == ToNatRight(xs)
    decreases n - |xs|
  {
    if |xs| >= n then xs else LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
  }

  /* Extends a sequence to a length that is a multiple of n. */
  opaque function SeqExtendMultiple(xs: seq<digit>, n: nat): (ys: seq<digit>)
    requires n > 0
    ensures |ys| % n == 0
    ensures ToNatRight(ys) == ToNatRight(xs)
  {
    var newLen := |xs| + n - (|xs| % n);
    LemmaSubModNoopRight(|xs| + n, |xs|, n);
    LemmaModBasicsAuto();
    assert newLen % n == 0;

    LemmaSeqNatBound(xs);
    LemmaPowIncreasesAuto();
    SeqExtend(xs, newLen)
  }

  /* Converts a nat to a sequence of a specified length. */
  function FromNatWithLen(n: nat, len: nat): (xs: seq<digit>)
    requires Pow(BASE(), len) > n
    ensures |xs| == len
    ensures ToNatRight(xs) == n
  {
    LemmaFromNatLen(n, len);
    LemmaNatSeqNat(n);
    SeqExtend(FromNat(n), len)
  }

  /* If the nat representation of a sequence is zero, then the sequence is a
  sequence of zeros. */
  @ResourceLimit("10e6")
  lemma LemmaSeqZero(xs: seq<digit>)
    requires ToNatRight(xs) == 0
    ensures forall i :: 0 <= i < |xs| ==> xs[i] == 0
  {
    if |xs| == 0 {
    } else {
      LemmaMulNonnegativeAuto();
      assert First(xs) == 0;

      LemmaMulNonzeroAuto();
      LemmaSeqZero(DropFirst(xs));
    }
  }

  /* Generates a sequence of zeros of a specified length. */
  opaque function SeqZero(len: nat): (xs: seq<digit>)
    ensures |xs| == len
    ensures forall i :: 0 <= i < |xs| ==> xs[i] == 0
    ensures ToNatRight(xs) == 0
  {
    LemmaPowPositive(BASE(), len);
    var xs := FromNatWithLen(0, len);
    LemmaSeqZero(xs);
    xs
  }

  /* If we start with a sequence, convert it to a nat, and convert it back to a
  sequence with the same length as the original sequence, we get the same
  sequence we started with. */
  lemma LemmaSeqNatSeq(xs: seq<digit>)
    ensures Pow(BASE(), |xs|) > ToNatRight(xs)
    ensures FromNatWithLen(ToNatRight(xs), |xs|) == xs
  {
    LemmaSeqNatBound(xs);
    if |xs| > 0 {
      calc {
        FromNatWithLen(ToNatRight(xs), |xs|) != xs;
        { LemmaSeqNeq(FromNatWithLen(ToNatRight(xs), |xs|), xs); }
        ToNatRight(FromNatWithLen(ToNatRight(xs), |xs|)) != ToNatRight(xs);
        ToNatRight(xs) != ToNatRight(xs);
        false;
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Addition and subtraction
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Adds two sequences. */
  function SeqAdd(xs: seq<digit>, ys: seq<digit>): (seq<digit>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := SeqAdd(xs, ys);
            |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then ([], 0)
    else
      var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
      var sum: int := Last(xs) + Last(ys) + cin;
      var (sum_out, cout) := if sum < BASE() then (sum, 0)
                             else (sum - BASE(), 1);
      (zs' + [sum_out], cout)
  }

  /* SeqAdd returns the same value as converting the sequences to nats, then
  adding them. */
  @IsolateAssertions
  lemma LemmaSeqAdd(xs: seq<digit>, ys: seq<digit>, zs: seq<digit>, cout: nat)
    requires |xs| == |ys|
    requires SeqAdd(xs, ys) == (zs, cout)
    ensures ToNatRight(xs) + ToNatRight(ys) == ToNatRight(zs) + cout * Pow(BASE(), |xs|)
  {
    if |xs| == 0 {
    } else {
      var pow := Pow(BASE(), |xs| - 1);
      var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
      var sum: int := Last(xs) + Last(ys) + cin;
      var z := if sum < BASE() then sum else sum - BASE();
      assert sum == z + cout * BASE();

      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(zs);
        ToNatLeft(zs);
        ToNatLeft(zs') + z * pow;
        { LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin); }
        ToNatLeft(DropLast(xs)) + ToNatLeft(DropLast(ys)) - cin * pow + z * pow;
        {
          LemmaMulEquality(sum, z + cout * BASE(), pow);
          assert sum * pow == (z + cout * BASE()) * pow;
          LemmaMulIsDistributiveAuto();
        }
        ToNatLeft(xs) + ToNatLeft(ys) - cout * BASE() * pow;
        {
          LemmaMulIsAssociative(cout, BASE(), pow);
        }
        ToNatLeft(xs) + ToNatLeft(ys) - cout * Pow(BASE(), |xs|);
        ToNatRight(xs) + ToNatRight(ys) - cout * Pow(BASE(), |xs|);
      }
    }
  }

  /* Subtracts two sequences. */
  function SeqSub(xs: seq<digit>, ys: seq<digit>): (seq<digit>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := SeqSub(xs, ys);
            |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then ([], 0)
    else
      var (zs, cin) := SeqSub(DropLast(xs), DropLast(ys));
      var (diff_out, cout) := if Last(xs) >= Last(ys) + cin
                              then (Last(xs) - Last(ys) - cin, 0)
                              else (BASE() + Last(xs) - Last(ys) - cin, 1);
      (zs + [diff_out], cout)
  }

  /* SeqSub returns the same value as converting the sequences to nats, then
  subtracting them. */
  @IsolateAssertions
  lemma LemmaSeqSub(xs: seq<digit>, ys: seq<digit>, zs: seq<digit>, cout: nat)
    requires |xs| == |ys|
    requires SeqSub(xs, ys) == (zs, cout)
    ensures ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|) == ToNatRight(zs)
  {
    if |xs| == 0 {
    } else {
      var pow := Pow(BASE(), |xs| - 1);
      var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
      var z := if Last(xs) >= Last(ys) + cin
      then Last(xs) - Last(ys) - cin
      else BASE() + Last(xs) - Last(ys) - cin;
      assert cout * BASE() + Last(xs) - cin - Last(ys) == z;

      LemmaToNatLeftEqToNatRightAuto();
      calc {
        ToNatRight(zs);
        ToNatLeft(zs);
        ToNatLeft(zs') + z * pow;
        { LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin); }
        ToNatLeft(DropLast(xs)) - ToNatLeft(DropLast(ys)) + cin * pow + z * pow;
        {
          LemmaMulEquality(cout * BASE() + Last(xs) - cin - Last(ys), z, pow);
          assert pow * (cout * BASE() + Last(xs) - cin - Last(ys)) == pow * z;
          LemmaMulIsDistributiveAuto();
        }
        ToNatLeft(xs) - ToNatLeft(ys) + cout * BASE() * pow;
        {
          LemmaMulIsAssociative(cout, BASE(), pow);
        }
        ToNatLeft(xs) - ToNatLeft(ys) + cout * Pow(BASE(), |xs|);
        ToNatRight(xs) - ToNatRight(ys) + cout * Pow(BASE(), |xs|);
      }
    }
  }

}
