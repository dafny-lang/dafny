

module Std.Termination {

  import opened Collections.Set
  import opened Collections.Multiset
  import opened Ordinal
  import Collections.Seq


  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TerminationMetric =
    | Bool(boolValue: bool)
    | Nat(natValue: nat)
    | Char(charValue: nat)
    | Ord(ordinalValue: ORDINAL)
      // No ordering on objects themselves, but commonly used in Repr set<object> values
    | Object(objectValue: object)
      // Also used to encode datatype structural inclusion
    | Seq(seqValue: seq<TerminationMetric>)
    | Set(setValue: set<TerminationMetric>)

      // Other kinds of Dafny values are valid here too,
      // and may be added in the future.

      // Lexicographic tuple.
    | Tuple(base: TerminationMetric, first: TerminationMetric, second: TerminationMetric)

      // The "top" value used in the definition of Dafny decreases clauses.
      // Only guaranteed to be above any value expressible in Dafny syntax.
    | Top

      // Never used by direct Dafny syntax, but very useful for simple dependencies.
    | Succ(original: TerminationMetric)
  {
    ghost predicate Valid()
      decreases this, 0
    {
      match this {
        case Succ(original) =>
          && original.Valid()
        case Set(setValue) =>
          && (forall tm <- setValue :: tm.Valid())
        case Seq(children) =>
          && (forall tm <- children :: tm.Valid())
        case Tuple(_, left, right) =>
          && left.Valid()
          && right.Valid()
          && base.Valid()
          && base.Ordinal() > right.Ordinal()
        case _ => true
      }
    }

    ghost opaque function Ordinal(): ORDINAL
      requires Valid()
      decreases this
    {
      match this {
        case Bool(boolValue) => if boolValue then 1 else 0
        case Nat(natValue) => natValue as ORDINAL
        case Char(charValue) => charValue as ORDINAL
        case Ord(ordinalValue) => ordinalValue
        case Object(objectValue) => 0
        case Set(setValue) => |setValue| as ORDINAL
        case Seq(seqValue) => MultisetOrdinal(this, multiset(seqValue))
        case Tuple(base, first, second) => Times(base.Ordinal(), first.Ordinal()) + second.Ordinal() + 1
        case Succ(original) => original.Ordinal() + 1
        case Top => Omega()
      }
    }

    ghost predicate DecreasesTo(other: TerminationMetric)
      requires Valid()
      requires other.Valid()
    {
      Ordinal() > other.Ordinal()
    }

    ghost predicate NonIncreasesTo(other: TerminationMetric)
      requires Valid()
      requires other.Valid()
    {
      Ordinal() >= other.Ordinal()
    }

    @IsolateAssertions
    static opaque ghost function MaxOrdinal(parent: TerminationMetric, s: multiset<TerminationMetric>): ORDINAL
      requires forall o <- s :: (parent decreases to o) && o.Valid()
      decreases parent, |s|, 0
      ensures forall o <- s :: MaxOrdinal(parent, s) >= o.Ordinal()
    {
      if s == multiset{} then
        0
      else
        var x := ExtractFromNonEmptyMultiset(s);
        Max(x.Ordinal(), MaxOrdinal(parent, s - multiset{x}))
    }

    // parent is a MaxOrdinal() parameter just to prove termination,
    // but doesn't affect the actual result.
    static lemma MaxOrdinalAnyParent(parent: TerminationMetric, parent': TerminationMetric, s: multiset<TerminationMetric>)
      requires forall o <- s :: o.Valid() && (parent decreases to o) && (parent' decreases to o)
      ensures MaxOrdinal(parent, s) == MaxOrdinal(parent', s)
    {
      reveal MaxOrdinal();
    }

    static ghost function MultisetOrdinal(parent: TerminationMetric, s: multiset<TerminationMetric>): ORDINAL
      requires forall o <- s :: (parent decreases to o) && o.Valid()
      decreases parent, |s|
    {
      MaxOrdinal(parent, s) + |s| as ORDINAL + 1
    }

    // parent is a MultisetOrdinal() parameter just to prove termination,
    // but doesn't affect the actual result.
    static lemma MultisetOrdinalAnyParent(parent: TerminationMetric, parent': TerminationMetric, s: multiset<TerminationMetric>)
      requires forall o <- s :: o.Valid() && (parent decreases to o) && (parent' decreases to o)
      ensures MultisetOrdinal(parent, s) == MultisetOrdinal(parent', s)
    {
      MaxOrdinalAnyParent(parent, parent', s);
    }

    static lemma MultisetOrdinalDecreasesToSubMultiset(parent: TerminationMetric, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: (parent decreases to o) && o.Valid()
      requires forall o <- right :: (parent decreases to o) && o.Valid()
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

      PlusIncreasingOnLeft(maxLeft, maxRight, |right| as ORDINAL + 1);
      PlusStrictlyIncreasingOnRight(maxLeft, |left| as ORDINAL + 1, |right| as ORDINAL + 1);
    }

    static lemma MaxOrdinalNonIncreases(parent: TerminationMetric, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: (parent decreases to o) && o.Valid()
      requires forall o <- right :: (parent decreases to o) && o.Valid()
      requires left > right
      ensures MaxOrdinal(parent, left) >= MaxOrdinal(parent, right)
    {
      reveal MaxOrdinal();
    }

    static lemma MaxOrdinalDecreasesIfAllDecrease(parent: TerminationMetric, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: (parent decreases to o) && o.Valid()
      requires forall o <- right :: (parent decreases to o) && o.Valid()
      requires left > right
      ensures MaxOrdinal(parent, left) >= MaxOrdinal(parent, right)
    {
      reveal MaxOrdinal();
    }

    lemma SetDecreasesTo(other: TerminationMetric)
      requires Valid()
      requires Set?
      requires other.Valid()
      requires other.Set?
      requires setValue > other.setValue
      ensures Ordinal() > other.Ordinal()
    {
      reveal Ordinal();
      LemmaSubsetSize(other.setValue, setValue);
    }

    lemma SeqDecreasesToSubSequence(other: TerminationMetric)
      requires Valid()
      requires Seq?
      requires other.Valid()
      requires other.Seq?
      requires multiset(seqValue) > multiset(other.seqValue)
      ensures Ordinal() > other.Ordinal()
    {
      reveal Ordinal();
      MultisetOrdinalAnyParent(this, other, multiset(other.seqValue));
      MultisetOrdinalDecreasesToSubMultiset(this, multiset(seqValue), multiset(other.seqValue));
    }

    lemma SeqDecreasesToProperPrefix(other: TerminationMetric, hi: nat)
      requires Valid()
      requires Seq?
      requires other.Valid()
      requires other.Seq?
      requires hi < |seqValue|
      requires seqValue[..hi] == other.seqValue
      ensures Ordinal() > other.Ordinal()
    {
      assert seqValue == seqValue[..hi] + seqValue[hi..];
      SeqDecreasesToSubSequence(other);
    }

    lemma SeqDecreasesToProperSuffix(other: TerminationMetric, lo: nat)
      requires Valid()
      requires Seq?
      requires other.Valid()
      requires other.Seq?
      requires 0 < lo <= |seqValue|
      requires seqValue[lo..] == other.seqValue
      ensures Ordinal() > other.Ordinal()
    {
      assert seqValue == seqValue[..lo] + seqValue[lo..];
      SeqDecreasesToSubSequence(other);
    }

    lemma SeqDecreasesToProperDeletion(other: TerminationMetric, lo: nat, hi: nat)
      requires Valid()
      requires Seq?
      requires other.Valid()
      requires other.Seq?
      requires 0 <= lo < hi <= |seqValue|
      requires seqValue[..lo] + seqValue[hi..] == other.seqValue
      ensures Ordinal() > other.Ordinal()
    {
      assert seqValue == seqValue[..lo] + seqValue[lo..hi] + seqValue[hi..];
      SeqDecreasesToSubSequence(other);
    }

    lemma SeqDecreasesToElement(other: TerminationMetric)
      requires Valid()
      requires Seq?
      requires other.Valid()
      requires other in seqValue
      ensures Ordinal() > other.Ordinal()
    {
      reveal Ordinal();
    }

    lemma TupleDecreasesToTuple(other: TerminationMetric)
      requires Valid()
      requires Tuple?
      requires other.Valid()
      requires other.Tuple?
      requires base == other.base
      requires
        || (first.Ordinal() > other.first.Ordinal())
        || (first.Ordinal() >= other.first.Ordinal() && second.Ordinal() > other.second.Ordinal())
      ensures Ordinal() > other.Ordinal()
    {
      reveal Ordinal();
      if first.Ordinal() > other.first.Ordinal() {
        TimesStrictlyIncreasingOnRight(base.Ordinal(), first.Ordinal(), other.first.Ordinal());
        RadixDecreases(base.Ordinal(), first.Ordinal(), other.first.Ordinal(), other.second.Ordinal());
      } else {
        PlusStrictlyIncreasingOnRight(Times(base.Ordinal(), first.Ordinal()), second.Ordinal(), other.second.Ordinal());
      }
      SuccStrictlyIncreasing(Times(base.Ordinal(), first.Ordinal()) + second.Ordinal(),
                             Times(base.Ordinal(), other.first.Ordinal()) + other.second.Ordinal());
    }

    lemma TupleNonIncreasesToTuple(other: TerminationMetric)
      requires Valid()
      requires Tuple?
      requires other.Valid()
      requires other.Tuple?
      requires base == other.base
      requires first.Ordinal() >= other.first.Ordinal()
      requires second.Ordinal() >= other.second.Ordinal()
      ensures Ordinal() >= other.Ordinal()
    {
      reveal Ordinal();
      if first.Ordinal() > other.first.Ordinal() || second.Ordinal() > other.second.Ordinal() {
        TupleDecreasesToTuple(other);
      }
    }

    lemma TupleDecreasesToFirst()
      requires Valid()
      requires Tuple?
      ensures Ordinal() > first.Ordinal()
    {
      reveal Ordinal();
      var term := Times(base.Ordinal(), first.Ordinal());
      PlusStrictlyIncreasingOnRight(term, second.Ordinal() + 1, 0);
      PlusIsAssociative(term, second.Ordinal(), 1);
      TimesIncreasingOnLeft(base.Ordinal(), 1, first.Ordinal());
      TimesLeftIdentity(first.Ordinal());
    }

    lemma TupleDecreasesToSecond()
      requires Valid()
      requires Tuple?
      ensures Ordinal() > second.Ordinal()
    {
      reveal Ordinal();
      PlusIncreasingOnLeft(Times(base.Ordinal(), first.Ordinal()), 0, second.Ordinal());
    }

    lemma SuccDecreasesTo(other: TerminationMetric)
      requires Valid()
      requires Succ?
      requires other.Valid()
      requires other.Succ?
      requires original.DecreasesTo(other.original)
      ensures DecreasesTo(other)
    {
      reveal Ordinal();
      SuccStrictlyIncreasing(original.Ordinal(), other.original.Ordinal());
    }

    lemma SuccNonIncreasesTo(other: TerminationMetric)
      requires Valid()
      requires Succ?
      requires other.Valid()
      requires other.Succ?
      requires original.NonIncreasesTo(other.original)
      ensures NonIncreasesTo(other)
    {
      reveal Ordinal();
      if original.Ordinal() > other.original.Ordinal() {
        SuccStrictlyIncreasing(original.Ordinal(), other.original.Ordinal());
      }
    }
  }

  ghost function TMBool(b: bool): (result: TerminationMetric)
    ensures result.Valid()
  {
    Bool(b)
  }

  ghost function TMNat(n: nat): (result: TerminationMetric)
    ensures result.Valid()
  {
    Nat(n)
  }

  ghost function TMOrdinal(o: ORDINAL): (result: TerminationMetric)
    ensures result.Valid()
  {
    Ord(o)
  }

  ghost function TMObject(o: object): (result: TerminationMetric)
    ensures result.Valid()
  {
    Object(o)
  }

  ghost function TMSet(children: set<TerminationMetric>): (result: TerminationMetric)
    requires forall tm <- children :: tm.Valid()
    ensures result.Valid()
  {
    Set(children)
  }

  ghost function TMSeq(children: seq<TerminationMetric>): (result: TerminationMetric)
    requires forall tm <- children :: tm.Valid()
    ensures result.Valid()
  {
    Seq(children)
  }

  @ResourceLimit("1e7")
  ghost function TMTuple(base: TerminationMetric, first: TerminationMetric, second: TerminationMetric): (result: TerminationMetric)
    requires first.Valid()
    requires second.Valid()
    requires base.Valid()
    requires base.Ordinal() > second.Ordinal()
    ensures result.Valid()
  {
    Tuple(base, first, second)
  }

  ghost function TMTupleOf(base: TerminationMetric, children: seq<TerminationMetric>): (result: TerminationMetric)
    requires base.Valid()
    requires children != []
    requires forall tm <- children :: tm.Valid() && base.Ordinal() > tm.Ordinal()
    ensures result.Valid()
  {
    if |children| == 1 then
      Seq.First(children)
    else
      TMTuple(base, TMTupleOf(base, Seq.DropLast(children)), Seq.Last(children))
  }

  const TMTop := Top

  ghost function TMSucc(tm: TerminationMetric): (result: TerminationMetric)
    requires tm.Valid()
    ensures result.Valid()
  {
    Succ(tm)
  }
}
