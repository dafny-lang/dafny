

module Std.Termination {

  import opened Collections.Set
  import opened Collections.Multiset
  import opened Ordinal
  import Collections.Seq


  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TerminationMetric =
    | Bool(boolValue: bool, height: nat)
    | Nat(natValue: nat, height: nat)
    | Char(charValue: nat, height: nat)
    | Ord(ordinalValue: ORDINAL, height: nat)
      // No ordering on objects themselves, but commonly used in Repr set<object> values
    | Object(objectValue: object, height: nat)
      // Also used to encode datatype structural inclusion
    | Seq(seqValue: seq<TerminationMetric>, height: nat)
    | Set(setValue: set<TerminationMetric>, height: nat)

      // Other kinds of Dafny values are valid here too,
      // and may be added in the future.

      // Lexicographic tuple.
    | Tuple(base: TerminationMetric, first: TerminationMetric, second: TerminationMetric, height: nat)

      // The "top" value used in the definition of Dafny decreases clauses.
      // Only guaranteed to be above any value expressible in Dafny syntax.
    | Top(height: nat)

      // Never used by direct Dafny syntax, but very useful for simple dependencies.
    | Succ(original: TerminationMetric, height: nat)
  {
    ghost predicate Valid()
      decreases height, 0
    {
      match this {
        case Succ(original, height) =>
          && height > original.height
          && original.Valid()
        case Set(setValue, height) =>
          && height > SetHeightSum(setValue)
          && (forall tm <- setValue :: tm.Valid())
        case Seq(children, height) =>
          && height > SeqHeightSum(children)
          && (forall tm <- children :: tm.Valid())
        case Tuple(_, left, right, height) =>
          && height > left.height
          && left.Valid()
          && height > right.height
          && right.Valid()
          && height > base.height
          && base.Valid()
          && base.Ordinal() > right.Ordinal()
        case _ => true
      }
    }

    ghost opaque function Ordinal(): ORDINAL
      requires Valid()
      decreases height
    {
      match this {
        case Bool(boolValue, _) => (if boolValue then 1 else 0) as ORDINAL
        case Nat(natValue, _) => natValue as ORDINAL
        case Char(charValue, _) => charValue as ORDINAL
        case Ord(ordinalValue, _) => ordinalValue
        case Object(objectValue, _) => 0
        case Set(setValue, _) => |setValue| as ORDINAL
        case Seq(seqValue, _) => MultisetOrdinal(height, multiset(seqValue))
        case Tuple(base, first, second, _) => Times(base.Ordinal(), first.Ordinal()) + second.Ordinal() + 1
        case Succ(original, _) => original.Ordinal() + 1
        case Top(_) => Omega()
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

    // TODO: Reuse Seq.FoldLeft?

    static ghost function SetHeightSum(s: set<TerminationMetric>): nat
      ensures forall o <- s :: SetHeightSum(s) > o.height
    {
      if s == {} then
        0
      else
        var o := ExtractFromNonEmptySet(s);
        o.height + 1 + SetHeightSum(s - {o})
    }

    static ghost function SeqHeightSum(s: seq<TerminationMetric>): nat
      ensures forall o <- s :: SeqHeightSum(s) > o.height
    {
      if s == [] then
        0
      else
        s[0].height + 1 + SeqHeightSum(s[1..])
    }

    @IsolateAssertions
    static opaque ghost function MaxOrdinal(height: nat, s: multiset<TerminationMetric>): ORDINAL
      requires forall o <- s :: height > o.height && o.Valid()
      decreases height, |s|, 0
      ensures forall o <- s :: MaxOrdinal(height, s) >= o.Ordinal()
    {
      if s == multiset{} then
        0
      else
        var x := ExtractFromNonEmptyMultiset(s);
        Max(x.Ordinal(), MaxOrdinal(height, s - multiset{x}))
    }

    // height is a MaxOrdinal() parameter just to prove termination,
    // but doesn't affect the actual result.
    static lemma MaxOrdinalAnyHeight(height: nat, height': nat, s: multiset<TerminationMetric>)
      requires forall o <- s :: o.Valid() && height > o.height && height' > o.height
      ensures MaxOrdinal(height, s) == MaxOrdinal(height', s)
    {
      reveal MaxOrdinal();
    }

    static ghost function MultisetOrdinal(height: nat, s: multiset<TerminationMetric>): ORDINAL
      requires forall o <- s :: height > o.height && o.Valid()
      decreases height, |s|
    {
      MaxOrdinal(height, s) + |s| as ORDINAL + 1
    }

    // height is a MultisetOrdinal() parameter just to prove termination,
    // but doesn't affect the actual result.
    static lemma MultisetOrdinalAnyHeight(height: nat, height': nat, s: multiset<TerminationMetric>)
      requires forall o <- s :: o.Valid() && height > o.height && height' > o.height
      ensures MultisetOrdinal(height, s) == MultisetOrdinal(height', s)
    {
      MaxOrdinalAnyHeight(height, height', s);
    }

    static lemma MultisetOrdinalDecreasesToSubMultiset(height: nat, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: o.Valid() && height > o.height
      requires forall o <- right :: o.Valid() && height > o.height
      requires left > right
      ensures MultisetOrdinal(height, left) > MultisetOrdinal(height, right)
    {
      var maxLeft := MaxOrdinal(height, left);
      var maxRight := MaxOrdinal(height, right);
      MaxOrdinalNonIncreases(height, left, right);

      assert maxLeft >= maxRight;
      LemmaSubmultisetSize(right, left);
      assert |left| > |right|;
      assert |left| as ORDINAL + 1 > |right| as ORDINAL + 1 ;

      PlusIncreasingOnLeft(maxLeft, maxRight, |right| as ORDINAL + 1);
      PlusStrictlyIncreasingOnRight(maxLeft, |left| as ORDINAL + 1, |right| as ORDINAL + 1);
    }

    static lemma MaxOrdinalNonIncreases(height: nat, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: o.Valid() && height > o.height
      requires forall o <- right :: o.Valid() && height > o.height
      requires left > right
      ensures MaxOrdinal(height, left) >= MaxOrdinal(height, right)
    {
      reveal MaxOrdinal();
    }

    static lemma MaxOrdinalDecreasesIfAllDecrease(height: nat, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: o.Valid() && height > o.height
      requires forall o <- right :: o.Valid() && height > o.height
      requires left > right
      ensures MaxOrdinal(height, left) >= MaxOrdinal(height, right)
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
      MultisetOrdinalDecreasesToSubMultiset(height, multiset(seqValue), multiset(other.seqValue));
      MultisetOrdinalAnyHeight(height, other.height, multiset(other.seqValue));
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
      TimesIdentity(first.Ordinal());
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
    Bool(b, 0)
  }

  ghost function TMNat(n: nat): (result: TerminationMetric)
    ensures result.Valid()
  {
    Nat(n, 0)
  }

  ghost function TMOrdinal(o: ORDINAL): (result: TerminationMetric)
    ensures result.Valid()
  {
    Ord(o, 0)
  }

  ghost function TMObject(o: object): (result: TerminationMetric)
    ensures result.Valid()
  {
    Object(o, 0)
  }

  ghost function TMSet(children: set<TerminationMetric>): (result: TerminationMetric)
    requires forall tm <- children :: tm.Valid()
    ensures result.Valid()
  {
    Set(children, TerminationMetric.SetHeightSum(children) + 1)
  }

  ghost function TMSeq(children: seq<TerminationMetric>): (result: TerminationMetric)
    requires forall tm <- children :: tm.Valid()
    ensures result.Valid()
  {
    Seq(children, TerminationMetric.SeqHeightSum(children) + 1)
  }

  @ResourceLimit("10e6")
  ghost function TMTuple(base: TerminationMetric, first: TerminationMetric, second: TerminationMetric): (result: TerminationMetric)
    requires first.Valid()
    requires second.Valid()
    requires base.Valid()
    requires base.Ordinal() > second.Ordinal()
    ensures result.Valid()
  {
    Tuple(base, first, second, first.height + second.height + base.height + 1)
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

  const TMTop := Top(0)

  ghost function TMSucc(tm: TerminationMetric): (result: TerminationMetric)
    requires tm.Valid()
    ensures result.Valid()
  {
    Succ(tm, tm.height + 1)
  }
}

module TerminationExample {

  import opened Std.Termination
  import opened Std.Ordinal

  // @IsolateAssertions
  // method Test() {
  //   var tm := TMNat(7);
  //   var tm2 := TMNat(8);
  //   assert tm2.Ordinal() > tm.Ordinal();

  //   var s1 := TMSeq([TMNat(1), TMNat(2), TMNat(3)]);
  //   var s2 := TMSeq([TMNat(2), TMNat(3)]);
  //   var s3 := TMSeq([TMNat(1), TMNat(2)]);
  //   var s4 := TMSeq([TMNat(1), TMNat(3)]);
  //   assert s1.seqValue[1..] == s2.seqValue;
  //   s1.SeqDecreasesToProperSuffix(s2, 1);
  //   assert s1.seqValue[..2] == s3.seqValue;
  //   s1.SeqDecreasesToProperPrefix(s3, 2);
  //   assert s1.seqValue[..1] + s1.seqValue[2..] == s4.seqValue;
  //   s1.SeqDecreasesToProperDeletion(s4, 1, 2);

  //   TMTuple(Omega(), tm2, tm2).TupleDecreasesToTuple(TMTuple(Omega(), tm, tm2));
  //   assert TMTuple(Omega(), tm2, tm2).Ordinal() > TMTuple(Omega(), tm, tm2).Ordinal();
  //   TMTuple(Omega(), tm2, tm2).TupleDecreasesToTuple(TMTuple(Omega(), tm2, tm));
  //   assert TMTuple(Omega(), tm2, tm2).Ordinal() > TMTuple(Omega(), tm2, tm).Ordinal();

  //   // Can't be verified
  //   // assert (Tuple(Omega(), tm, tm2).Ordinal() > Tuple(Omega(), tm2, tm).Ordinal());
  // }

  method {:test} Child() {
    var x: nat := 10;
    var child := TMNat(x);
    var parent := TMSeq([child]);
    assert parent.Ordinal() > child.Ordinal() by {
      reveal TerminationMetric.Ordinal();
    }
  }

  method {:test} Succ() {
    reveal TerminationMetric.Ordinal();
    assert forall x: TerminationMetric | x.Valid() :: TMSucc(x).DecreasesTo(TMNat(0));
  }

  method {:test} NestedLoop() {
    reveal TerminationMetric.Ordinal();
    var x: nat := 10;
    var y: nat := 10;
    var tm := TMTuple(TMTop, TMNat(x), TMNat(y));
    while 0 < x && 0 < y
      invariant tm.Valid()
      invariant tm == TMTuple(TMTop, TMNat(x), TMNat(y))
      decreases tm.Ordinal()
    {
      ghost var tmBefore := tm;
      ghost var yBefore := y;
      if y == 0 {
        if x == 0 {
          break;
        } else {
          x := x - 1;
          y := 10;

          tm := TMTuple(TMTop, TMNat(x), TMNat(y));
          tmBefore.TupleDecreasesToTuple(tm);
        }
      } else {
        y := y - 1;

        tm := TMTuple(TMTop, TMNat(x), TMNat(y));
        tmBefore.TupleDecreasesToTuple(tm);
      }
    }
  }
}

module Std.Ordinal {
  ghost function {:axiom} Omega(): ORDINAL
    ensures !Omega().IsNat
    ensures Omega().IsLimit
    ensures forall other: ORDINAL | other.IsLimit && other != 0 :: Omega() <= other

  // TODO: Prove some of these via transfinite induction?

  // Additional axioms about addition

  lemma {:axiom} Succ(a: ORDINAL, b: ORDINAL)
    requires a > b
    ensures a >= b + 1

  lemma {:axiom} SuccStrictlyIncreasing(a: ORDINAL, b: ORDINAL)
    requires a > b
    ensures a + 1 > b + 1

  lemma {:axiom} PlusStrictlyIncreasingOnRight(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    requires right > right'
    ensures left + right > left + right'

  lemma {:axiom} PlusIncreasingOnLeft(left: ORDINAL, left': ORDINAL, right: ORDINAL)
    requires left >= left'
    ensures left + right >= left' + right

  lemma {:axiom} PlusIsAssociative(x: ORDINAL, y: ORDINAL, z: ORDINAL)
    ensures (x + y) + z == x + (y + z)

  // Multiplication and axioms about multiplication

  ghost function {:axiom} Times(left: ORDINAL, right: ORDINAL): (result: ORDINAL)

  lemma {:axiom} TimesIdentity(o: ORDINAL)
    ensures Times(1, o) == o
    ensures Times(o, 1) == o

  lemma {:axiom} TimesStrictlyIncreasingOnRight(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    requires left > 0
    requires right > right'
    ensures Times(left, right) > Times(left, right')

  lemma {:axiom} TimesIncreasingOnLeft(left: ORDINAL, left': ORDINAL, right: ORDINAL)
    requires left >= left'
    ensures Times(left, right) > Times(left', right)

  lemma {:axiom} TimesDistributesOnLeft(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    ensures Times(left, right + right') == Times(left, right) + Times(left, right')

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
    TimesIdentity(base);
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
