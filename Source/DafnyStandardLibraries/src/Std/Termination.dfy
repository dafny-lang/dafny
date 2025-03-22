

module Std.Termination {

  import opened Collections.Set
  import opened Collections.Multiset
  import opened Ordinal

  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TerminationMetric =
    | TMBool(boolValue: bool, height: nat)
    | TMNat(natValue: nat, height: nat)
    | TMChar(charValue: nat, height: nat)
    // No ordering on objects themselves, but commonly used in Repr set<object> values
    | TMObject(objectValue: object, height: nat)
    | TMSeq(seqValue: seq<TerminationMetric>, height: nat)
    | TMSet(setValue: set<TerminationMetric>, height: nat)
    | TMDatatype(children: seq<TerminationMetric>, height: nat)

    // Other kinds of Dafny values are valid here too,
    // and may be added in the future.

    | TMTuple(base: ORDINAL, first: TerminationMetric, second: TerminationMetric, height: nat)
  {
    ghost predicate Valid() {
      match this {
        case TMSet(setValue, height) =>
          && (forall tm <- setValue :: tm.Valid())
          && height > SetHeightSum(setValue)
        case TMSeq(children, height) =>
          && (forall tm <- children :: tm.Valid())
          && height > SeqHeightSum(children)
        case TMDatatype(children, height) =>
          && (forall tm <- children :: tm.Valid())
          && height > SeqHeightSum(children)
        case TMTuple(_, left, right, height) =>
          && left.Valid()
          && height > left.height
          && right.Valid()
          && height > right.height
        case _ => true
      }
    }

    ghost opaque function Ordinal(): ORDINAL 
      requires Valid()
      decreases height
      // Ensuring all ordinals are at least one makes the math much easier
      ensures Ordinal() > 0
    {
      match this {
        case TMBool(boolValue, _) => (if boolValue then 2 else 1) as ORDINAL
        case TMNat(natValue, _) => natValue as ORDINAL + 1 
        case TMChar(charValue, _) => charValue as ORDINAL + 1
        case TMSet(setValue, _) => |setValue| as ORDINAL + 1
        case TMSeq(seqValue, _) => MultisetOrdinal(height, multiset(seqValue))
        case TMObject(objectValue, _) => 1
        case TMDatatype(children, _) => MaxOrdinal(height, multiset(children)) + 1
        case TMTuple(base, first, second, _) => Times(base, first.Ordinal()) + second.Ordinal()
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
    static ghost function MaxOrdinal(height: nat, s: multiset<TerminationMetric>): ORDINAL
      requires forall o <- s :: o.Valid() && height > o.height
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
    {}

    static ghost function MultisetOrdinal(height: nat, s: multiset<TerminationMetric>): ORDINAL
      requires forall o <- s :: o.Valid() && height > o.height
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

    static ghost function ExtractFromNonEmptyMultiset<T>(s: multiset<T>): (x: T)
      requires |s| != 0
      ensures x in s
    {
      var x :| x in s;
      x
    }

    static lemma MaxOrdinalNonIncreases(height: nat, left: multiset<TerminationMetric>, right: multiset<TerminationMetric>)
      requires forall o <- left :: o.Valid() && height > o.height
      requires forall o <- right :: o.Valid() && height > o.height
      requires left > right
      ensures MaxOrdinal(height, left) >= MaxOrdinal(height, right)
    {}

    lemma SetDecreasesTo(other: TerminationMetric)
      requires Valid()
      requires TMSet?
      requires other.Valid()
      requires other.TMSet?
      requires setValue > other.setValue
      ensures Ordinal() > other.Ordinal()
    {
      reveal Ordinal();
      LemmaSubsetSize(other.setValue, setValue);
    }

    lemma SeqDecreasesToSubSequence(other: TerminationMetric)
      requires Valid()
      requires TMSeq?
      requires other.Valid()
      requires other.TMSeq?
      requires multiset(seqValue) > multiset(other.seqValue)
      ensures Ordinal() > other.Ordinal()
    {
      reveal Ordinal();
      MultisetOrdinalDecreasesToSubMultiset(height, multiset(seqValue), multiset(other.seqValue));
      MultisetOrdinalAnyHeight(height, other.height, multiset(other.seqValue));
    }

    lemma SeqDecreasesToProperPrefix(other: TerminationMetric, hi: nat)
      requires Valid()
      requires TMSeq?
      requires other.Valid()
      requires other.TMSeq?
      requires hi < |seqValue|
      requires seqValue[..hi] == other.seqValue
      ensures Ordinal() > other.Ordinal()
    {
      assert seqValue == seqValue[..hi] + seqValue[hi..];
      SeqDecreasesToSubSequence(other);
    }

    lemma SeqDecreasesToProperSuffix(other: TerminationMetric, lo: nat)
      requires Valid()
      requires TMSeq?
      requires other.Valid()
      requires other.TMSeq?
      requires 0 < lo <= |seqValue| 
      requires seqValue[lo..] == other.seqValue
      ensures Ordinal() > other.Ordinal()
    {
      assert seqValue == seqValue[..lo] + seqValue[lo..];
      SeqDecreasesToSubSequence(other);
    }

    lemma SeqDecreasesToProperDeletion(other: TerminationMetric, lo: nat, hi: nat)
      requires Valid()
      requires TMSeq?
      requires other.Valid()
      requires other.TMSeq?
      requires 0 <= lo < hi <= |seqValue|
      requires seqValue[..lo] + seqValue[hi..] == other.seqValue
      ensures Ordinal() > other.Ordinal()
    {
      assert seqValue == seqValue[..lo] + seqValue[lo..hi] + seqValue[hi..];
      SeqDecreasesToSubSequence(other);
    }

    lemma TupleDecreasesTo(other: TerminationMetric)
      requires Valid()
      requires TMTuple?
      requires other.Valid()
      requires other.TMTuple?
      requires base == other.base
      requires 
        || (first.Ordinal() > other.first.Ordinal() && base > other.second.Ordinal())
        || (first == other.first                    && second.Ordinal() > other.second.Ordinal())
      ensures Ordinal() > other.Ordinal()
    {
      reveal Ordinal();
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

  ghost function Nat(n: nat): (result: TerminationMetric)
    ensures result.Valid()
    ensures result.Ordinal() < Omega()
  {
    reveal TerminationMetric.Ordinal();
    TMNat(n, 0)
  }

  ghost function Seq(children: seq<TerminationMetric>): (result: TerminationMetric)
    requires forall tm <- children :: tm.Valid()
    ensures result.Valid()
  {
    TMSeq(children, TerminationMetric.SeqHeightSum(children) + 1)
  }

  ghost function Datatype(children: seq<TerminationMetric>): (result: TerminationMetric)
    requires forall tm <- children :: tm.Valid()
    ensures result.Valid()
  {
    TMDatatype(children, TerminationMetric.SeqHeightSum(children) + 1)
  }

  ghost function Tuple(base: ORDINAL, first: TerminationMetric, second: TerminationMetric): (result: TerminationMetric)
    requires first.Valid()
    requires second.Valid()
    ensures result.Valid()
  {
    TMTuple(base, first, second, first.height + second.height + 1)
  }
}

module TerminationExample {

  import opened Std.Termination
  import opened Std.Ordinal

  @IsolateAssertions
  method Test() {
    var tm := Nat(7);
    var tm2 := Nat(8);
    assert tm2.Ordinal() > tm.Ordinal() by {
      reveal TerminationMetric.Ordinal();
    }

    var s1 := Seq([Nat(1), Nat(2), Nat(3)]);
    var s2 := Seq([Nat(2), Nat(3)]);
    var s3 := Seq([Nat(1), Nat(2)]);
    var s4 := Seq([Nat(1), Nat(3)]);
    assert s1.seqValue[1..] == s2.seqValue;
    s1.SeqDecreasesToProperSuffix(s2, 1);
    assert s1.seqValue[..2] == s3.seqValue;
    s1.SeqDecreasesToProperPrefix(s3, 2);
    assert s1.seqValue[..1] + s1.seqValue[2..] == s4.seqValue;
    s1.SeqDecreasesToProperDeletion(s4, 1, 2);

    Tuple(Omega(), tm2, tm2).TupleDecreasesTo(Tuple(Omega(), tm, tm2));
    assert Tuple(Omega(), tm2, tm2).Ordinal() > Tuple(Omega(), tm, tm2).Ordinal();
    Tuple(Omega(), tm2, tm2).TupleDecreasesTo(Tuple(Omega(), tm2, tm));
    assert Tuple(Omega(), tm2, tm2).Ordinal() > Tuple(Omega(), tm2, tm).Ordinal();

    // Can't be verified
    // assert (Tuple(Omega(), tm, tm2).Ordinal() > Tuple(Omega(), tm2, tm).Ordinal());
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
