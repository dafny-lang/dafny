

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
    // No ordering on objects themselves, but commonly used in Repr set<object> values
    | Object(objectValue: object, height: nat)
    | Seq(seqValue: seq<TerminationMetric>, height: nat)
    | Set(setValue: set<TerminationMetric>, height: nat)
    | Datatype(children: seq<TerminationMetric>, height: nat)

    // Other kinds of Dafny values are valid here too,
    // and may be added in the future.

    // 
    | Tuple(base: ORDINAL, first: TerminationMetric, second: TerminationMetric, height: nat)
  {
    ghost predicate Valid()
      decreases height, 0
    {
      match this {
        case Set(setValue, height) =>
          && height > SetHeightSum(setValue)
          && (forall tm <- setValue :: tm.Valid())
        case Seq(children, height) =>
          && height > SeqHeightSum(children)
          && (forall tm <- children :: tm.Valid())
        case Datatype(children, height) =>
          && height > SeqHeightSum(children)
          && (forall tm <- children :: tm.Valid())
        case Tuple(_, left, right, height) =>
          && height > left.height
          && left.Valid()
          && height > right.height
          && right.Valid()
          && base > right.Ordinal()
        case _ => true
      }
    }

    ghost function Ordinal(): ORDINAL 
      requires Valid()
      decreases height
      // Ensuring all ordinals are at least one makes the math much easier
      ensures Ordinal() > 0
    {
      match this {
        case Bool(boolValue, _) => (if boolValue then 2 else 1) as ORDINAL
        case Nat(natValue, _) => natValue as ORDINAL + 1 
        case Char(charValue, _) => charValue as ORDINAL + 1
        case Set(setValue, _) => |setValue| as ORDINAL + 1
        case Seq(seqValue, _) => MultisetOrdinal(height, multiset(seqValue))
        case Object(objectValue, _) => 1
        case Datatype(children, _) => MaxOrdinal(height, multiset(children)) + 1
        case Tuple(base, first, second, _) => Times(base, first.Ordinal()) + second.Ordinal()
      }
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

    lemma SetDecreasesTo(other: TerminationMetric)
      requires Valid()
      requires Set?
      requires other.Valid()
      requires other.Set?
      requires setValue > other.setValue
      ensures Ordinal() > other.Ordinal()
    {
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

    lemma TupleDecreasesTo(other: TerminationMetric)
      requires Valid()
      requires Tuple?
      requires other.Valid()
      requires other.Tuple?
      requires base == other.base
      requires 
        || (first.Ordinal() > other.first.Ordinal())
        || (first == other.first                    && second.Ordinal() > other.second.Ordinal())
      ensures Ordinal() > other.Ordinal()
    {
      if first == other.first {
        TimesStrictlyIncreasingOnRight(Omega(), first.Ordinal(), 0);
        var term := Times(base, first.Ordinal());
        PlusStrictlyIncreasingOnRight(term, second.Ordinal(), other.second.Ordinal());
      } else {
        TimesStrictlyIncreasingOnRight(base, first.Ordinal(), other.first.Ordinal());
        RadixDecreases(base, first.Ordinal(), other.first.Ordinal(), other.second.Ordinal());
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

  ghost function TMDatatype(children: seq<TerminationMetric>): (result: TerminationMetric)
    requires forall tm <- children :: tm.Valid()
    ensures result.Valid()
  {
    Datatype(children, TerminationMetric.SeqHeightSum(children) + 1)
  }

  ghost function TMTuple(base: ORDINAL, first: TerminationMetric, second: TerminationMetric): (result: TerminationMetric)
    requires first.Valid()
    requires second.Valid()
    requires base > second.Ordinal();
    ensures result.Valid()
  {
    Tuple(base, first, second, first.height + second.height + 1)
  }

  ghost function TMTupleOf(base: ORDINAL, children: seq<TerminationMetric>): (result: TerminationMetric)
    requires children != []
    requires forall tm <- children :: tm.Valid() && base > tm.Ordinal()
    ensures result.Valid()
  {
    if |children| == 1 then
      Seq.First(children)
    else
      TMTuple(base, TMTupleOf(base, Seq.DropLast(children)), Seq.Last(children))
  }
}

module TerminationExample {

  import opened Std.Termination
  import opened Std.Ordinal

  @IsolateAssertions
  method Test() {
    var tm := TMNat(7);
    var tm2 := TMNat(8);
    assert tm2.Ordinal() > tm.Ordinal();

    var s1 := TMSeq([TMNat(1), TMNat(2), TMNat(3)]);
    var s2 := TMSeq([TMNat(2), TMNat(3)]);
    var s3 := TMSeq([TMNat(1), TMNat(2)]);
    var s4 := TMSeq([TMNat(1), TMNat(3)]);
    assert s1.seqValue[1..] == s2.seqValue;
    s1.SeqDecreasesToProperSuffix(s2, 1);
    assert s1.seqValue[..2] == s3.seqValue;
    s1.SeqDecreasesToProperPrefix(s3, 2);
    assert s1.seqValue[..1] + s1.seqValue[2..] == s4.seqValue;
    s1.SeqDecreasesToProperDeletion(s4, 1, 2);

    TMTuple(Omega(), tm2, tm2).TupleDecreasesTo(TMTuple(Omega(), tm, tm2));
    assert TMTuple(Omega(), tm2, tm2).Ordinal() > TMTuple(Omega(), tm, tm2).Ordinal();
    TMTuple(Omega(), tm2, tm2).TupleDecreasesTo(TMTuple(Omega(), tm2, tm));
    assert TMTuple(Omega(), tm2, tm2).Ordinal() > TMTuple(Omega(), tm2, tm).Ordinal();

    // Can't be verified
    // assert (Tuple(Omega(), tm, tm2).Ordinal() > Tuple(Omega(), tm2, tm).Ordinal());
  }

  method {:test} NestedLoop() {
    var x: nat := 10;
    var y: nat := 10;
    var tm := TMTuple(Omega(), TMNat(x), TMNat(y));
    while 0 < x && 0 < y
      invariant tm.Valid()
      invariant tm == TMTuple(Omega(), TMNat(x), TMNat(y));
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

          tm := TMTuple(Omega(), TMNat(x), TMNat(y));
          tmBefore.TupleDecreasesTo(tm);
        }
      } else {
        y := y - 1;

        tm := TMTuple(Omega(), TMNat(x), TMNat(y));
        tmBefore.TupleDecreasesTo(tm);
      }
    }
  }
}

module Std.Ordinal {
  ghost function {:axiom} Omega(): ORDINAL 
      ensures !Omega().IsNat
      ensures Omega().IsLimit
      ensures forall other: ORDINAL | other.IsLimit && other != 0 :: Omega() <= other

  // Additional axioms about addition

  lemma {:axiom} Succ(a: ORDINAL, b: ORDINAL) 
    requires a > b
    ensures a >= b + 1

  lemma {:axiom} SuccAndGreaterThan(a: ORDINAL, b: ORDINAL) 
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
