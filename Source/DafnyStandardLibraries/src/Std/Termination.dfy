/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Std.Termination {

  import opened Collections.Set
  import opened Collections.Multiset
  import opened Ordinal
  import Collections.Seq

  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TerminationMetric =
    | TMBool(boolValue: bool)
    | TMNat(natValue: nat)
    | TMChar(charValue: nat)
    | TMOrdinal(ordinalValue: ORDINAL)
      // No ordering on objects themselves, but commonly used in Repr set<object> values
    | TMObject(objectValue: object)
      // Also used to encode datatype structural inclusion
    | TMSeq(seqValue: seq<TerminationMetric>)
    | TMSet(setValue: set<TerminationMetric>)

      // Other kinds of Dafny values are valid here too,
      // and may be added in the future.

      // Lexicographic tuple.
    | TMTuple(base: TerminationMetric, first: TerminationMetric, second: TerminationMetric)

      // The "top" value used in the definition of Dafny decreases clauses.
      // Only guaranteed to be above any value expressible in Dafny syntax.
    | TMTop

      // Never used by direct Dafny syntax, but very useful for simple dependencies.
      // Represents a metric value immediately above another one.
    | TMSucc(original: TerminationMetric)
  {
    ghost opaque function Ordinal(): ORDINAL
      decreases this
    {
      match this {
        case TMBool(boolValue) => if boolValue then 1 else 0
        case TMNat(natValue) => natValue as ORDINAL
        case TMChar(charValue) => charValue as ORDINAL
        case TMOrdinal(ordinalValue) => ordinalValue
        case TMObject(objectValue) => 0
        case TMSet(setValue) => |setValue| as ORDINAL
        case TMSeq(seqValue) => MultisetOrdinal(this, multiset(seqValue))
        case TMTuple(base, first, second) => Times(base.Ordinal(), first.Ordinal()) + second.Ordinal() + 1
        case TMSucc(original) => original.Ordinal() + 1
        case TMTop => Omega()
      }
    }

    ghost predicate DecreasesTo(other: TerminationMetric)
    {
      Ordinal() > other.Ordinal()
    }

    ghost predicate NonIncreasesTo(other: TerminationMetric)
    {
      Ordinal() >= other.Ordinal()
    }

    // parent is a MaxOrdinal() parameter just to prove termination,
    // but doesn't affect the actual result.
    static opaque ghost function MaxOrdinal(parent: TerminationMetric, s: multiset<TerminationMetric>): ORDINAL
      requires forall o <- s :: parent decreases to o
      decreases parent, |s|, 0
      ensures forall o <- s :: MaxOrdinal(parent, s) >= o.Ordinal()
    {
      if s == multiset{} then
        0
      else
        var x := ExtractFromNonEmptyMultiset(s);
        Max(x.Ordinal(), MaxOrdinal(parent, s - multiset{x}))
    }

    // Proof that parent is a MaxOrdinal() parameter just to prove termination,
    // but doesn't affect the actual result.
    static lemma MaxOrdinalAnyParent(parent: TerminationMetric, parent': TerminationMetric, s: multiset<TerminationMetric>)
      requires forall o <- s :: (parent decreases to o) && (parent' decreases to o)
      ensures MaxOrdinal(parent, s) == MaxOrdinal(parent', s)
    {
      reveal MaxOrdinal();
    }

    static ghost function MultisetOrdinal(parent: TerminationMetric, s: multiset<TerminationMetric>): ORDINAL
      requires forall o <- s :: parent decreases to o
      decreases parent, |s|
    {
      MaxOrdinal(parent, s) + |s| as ORDINAL + 1
    }

    // parent is a MultisetOrdinal() parameter just to prove termination,
    // but doesn't affect the actual result.
    static lemma MultisetOrdinalAnyParent(parent: TerminationMetric, parent': TerminationMetric, s: multiset<TerminationMetric>)
      requires forall o <- s :: (parent decreases to o) && (parent' decreases to o)
      ensures MultisetOrdinal(parent, s) == MultisetOrdinal(parent', s)
    {
      MaxOrdinalAnyParent(parent, parent', s);
    }

    static lemma MultisetOrdinalDecreasesToSubMultiset(parent: TerminationMetric, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: parent decreases to o
      requires forall o <- right :: parent decreases to o
      requires left > right
      ensures MultisetOrdinal(parent, left) > MultisetOrdinal(parent, right)
    {
      var maxLeft := MaxOrdinal(parent, left);
      var maxRight := MaxOrdinal(parent, right);
      MaxOrdinalNonIncreases(parent, left, right);

      assert maxLeft >= maxRight;
      LemmaSubmultisetSize(right, left);
      assert |left| > |right|;
      assert |left| as ORDINAL + 1 > |right| as ORDINAL + 1 ;

      PlusIncreasingOnLeft(maxRight, maxLeft, |right| as ORDINAL + 1);
      PlusStrictlyIncreasingOnRight(maxLeft, |right| as ORDINAL + 1, |left| as ORDINAL + 1);
    }

    static lemma MaxOrdinalNonIncreases(parent: TerminationMetric, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: parent decreases to o
      requires forall o <- right :: parent decreases to o
      requires left > right
      ensures MaxOrdinal(parent, left) >= MaxOrdinal(parent, right)
    {
      reveal MaxOrdinal();
    }

    static lemma MaxOrdinalDecreasesIfAllDecrease(parent: TerminationMetric, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: parent decreases to o
      requires forall o <- right :: parent decreases to o
      requires left > right
      ensures MaxOrdinal(parent, left) >= MaxOrdinal(parent, right)
    {
      reveal MaxOrdinal();
    }

    lemma SetDecreasesTo(other: TerminationMetric)
      requires TMSet?
      requires other.TMSet?
      requires setValue > other.setValue
      ensures DecreasesTo(other)
    {
      reveal Ordinal();
      LemmaSubsetSize(other.setValue, setValue);
    }

    lemma SeqDecreasesToSubSequence(other: TerminationMetric)
      requires TMSeq?
      requires other.TMSeq?
      requires multiset(seqValue) > multiset(other.seqValue)
      ensures DecreasesTo(other)
    {
      reveal Ordinal();
      MultisetOrdinalAnyParent(this, other, multiset(other.seqValue));
      MultisetOrdinalDecreasesToSubMultiset(this, multiset(seqValue), multiset(other.seqValue));
    }

    lemma SeqDecreasesToProperPrefix(other: TerminationMetric, hi: nat)
      requires TMSeq?
      requires other.TMSeq?
      requires hi < |seqValue|
      requires seqValue[..hi] == other.seqValue
      ensures DecreasesTo(other)
    {
      assert seqValue == seqValue[..hi] + seqValue[hi..];
      SeqDecreasesToSubSequence(other);
    }

    lemma SeqDecreasesToProperSuffix(other: TerminationMetric, lo: nat)
      requires TMSeq?
      requires other.TMSeq?
      requires 0 < lo <= |seqValue|
      requires seqValue[lo..] == other.seqValue
      ensures DecreasesTo(other)
    {
      assert seqValue == seqValue[..lo] + seqValue[lo..];
      SeqDecreasesToSubSequence(other);
    }

    lemma SeqDecreasesToProperDeletion(other: TerminationMetric, lo: nat, hi: nat)
      requires TMSeq?
      requires other.TMSeq?
      requires 0 <= lo < hi <= |seqValue|
      requires seqValue[..lo] + seqValue[hi..] == other.seqValue
      ensures DecreasesTo(other)
    {
      assert seqValue == seqValue[..lo] + seqValue[lo..hi] + seqValue[hi..];
      SeqDecreasesToSubSequence(other);
    }

    lemma SeqDecreasesToElement(other: TerminationMetric)
      requires TMSeq?
      requires other in seqValue
      ensures DecreasesTo(other)
    {
      reveal Ordinal();
    }

    lemma TupleDecreasesToTuple(other: TerminationMetric)
      requires TMTuple?
      requires other.TMTuple?
      requires base == other.base
      requires
        && other.base.DecreasesTo(other.second)
        && (
             || first.DecreasesTo(other.first)
             || (first.NonIncreasesTo(other.first) && second.DecreasesTo(other.second)))
      ensures DecreasesTo(other)
    {
      reveal Ordinal();
      if first.DecreasesTo(other.first) {
        TimesStrictlyIncreasingOnRight(base.Ordinal(), other.first.Ordinal(), first.Ordinal());
        RadixStrictlyIncreasing(base.Ordinal(), other.first.Ordinal(), first.Ordinal(), other.second.Ordinal());
      } else {
        PlusStrictlyIncreasingOnRight(Times(base.Ordinal(), first.Ordinal()), other.second.Ordinal(), second.Ordinal());
      }
      SuccStrictlyIncreasing(Times(base.Ordinal(), other.first.Ordinal()) + other.second.Ordinal(),
                             Times(base.Ordinal(), first.Ordinal()) + second.Ordinal());
    }

    lemma TupleNonIncreasesToTuple(other: TerminationMetric)
      requires TMTuple?
      requires other.TMTuple?
      requires base == other.base
      requires other.base.DecreasesTo(other.second)
      requires first.NonIncreasesTo(other.first)
      requires second.NonIncreasesTo(other.second)
      ensures NonIncreasesTo(other)
    {
      reveal Ordinal();
      if first.DecreasesTo(other.first) || second.DecreasesTo(other.second) {
        TupleDecreasesToTuple(other);
      }
    }

    lemma TupleDecreasesToFirst()
      requires TMTuple?
      requires base.DecreasesTo(second)
      ensures DecreasesTo(first)
    {
      reveal Ordinal();
      var term := Times(base.Ordinal(), first.Ordinal());
      PlusStrictlyIncreasingOnRight(term, 0, second.Ordinal() + 1);
      PlusIsAssociative(term, second.Ordinal(), 1);
      TimesIncreasingOnLeft(1, base.Ordinal(), first.Ordinal());
      TimesLeftIdentity(first.Ordinal());
    }

    lemma TupleDecreasesToSecond()
      requires TMTuple?
      requires base.DecreasesTo(second)
      ensures DecreasesTo(second)
    {
      reveal Ordinal();
      PlusIncreasingOnLeft(0, Times(base.Ordinal(), first.Ordinal()), second.Ordinal());
    }

    lemma SuccDecreasesToSucc(other: TerminationMetric)
      requires TMSucc?
      requires other.TMSucc?
      requires original.DecreasesTo(other.original)
      ensures DecreasesTo(other)
    {
      reveal Ordinal();
      SuccStrictlyIncreasing(other.original.Ordinal(), original.Ordinal());
    }

    lemma SuccNonIncreasesToSucc(other: TerminationMetric)
      requires TMSucc?
      requires other.TMSucc?
      requires original.NonIncreasesTo(other.original)
      ensures NonIncreasesTo(other)
    {
      reveal Ordinal();
      if original.Ordinal() > other.original.Ordinal() {
        SuccStrictlyIncreasing(other.original.Ordinal(), original.Ordinal());
      }
    }

    lemma SuccDecreasesToOriginal()
      requires TMSucc?
      ensures DecreasesTo(original)
    {
      reveal Ordinal();
    }
  }
}
