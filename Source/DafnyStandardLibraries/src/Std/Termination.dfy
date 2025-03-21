

module Std.Termination {

  import opened Collections.Set
  import opened Ordinal

  ghost function Nat(n: nat): (result: TerminationMetric)
    ensures result.Valid()
  {
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

  ghost function Tuple(first: TerminationMetric, second: TerminationMetric): (result: LexicographicTuple)
    requires first.Valid()
    requires second.Valid()
    ensures result.Valid()
  {
    LexicographicTuple(first, second)
  }

  datatype LexicographicTuple = LexicographicTuple(first: TerminationMetric, second: TerminationMetric) {
    ghost predicate Valid() {
      first.Valid() && second.Valid()
    }

    ghost function Ordinal(): ORDINAL
      requires Valid()
      decreases this
    {
      Times(Omega(), first.Ordinal() as ORDINAL) + second.Ordinal() as ORDINAL
    }

    @ResourceLimit("0")
    lemma DecreasesTo(other: LexicographicTuple)
      requires Valid()
      requires other.Valid()
      requires 
        || first.Ordinal() > other.first.Ordinal()
        || (first == other.first && second.Ordinal() > other.second.Ordinal())
      ensures Ordinal() > other.Ordinal()
    {
      if first == other.first {
        TimesStrictlyIncreasingOnRight(Omega(), first.Ordinal() as ORDINAL, 0);
        var term := Times(Omega(), first.Ordinal() as ORDINAL);
        AddStrictlyIncreasingOnRight(term, second.Ordinal() as ORDINAL, other.second.Ordinal() as ORDINAL);
      } else {
        TimesStrictlyIncreasingOnRight(Omega(), first.Ordinal() as ORDINAL, other.first.Ordinal() as ORDINAL);
        RadixDecreases(Omega(), first.Ordinal() as ORDINAL, other.first.Ordinal() as ORDINAL, other.second.Ordinal() as ORDINAL);
      }
    }
  }

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
        case _ => true
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

    static ghost function SeqOrdinal(height: nat, s: seq<TerminationMetric>): nat
      requires forall o <- s :: o.Valid() && height > o.height
      decreases height, |s|
      ensures forall o <- s :: SeqOrdinal(height, s) > o.Ordinal()
    {
      if s == [] then
        0
      else
        s[0].Ordinal() + 1 + SeqOrdinal(height, s[1..])
    }

    // height is a SeqOrdinal() parameter just to prove termination,
    // but doesn't affect the actual result.
    lemma SeqOrdinalAnyHeight(height: nat, height': nat, s: seq<TerminationMetric>)
      requires forall o <- s :: o.Valid() && height > o.height && height' > o.height
      ensures SeqOrdinal(height, s) == SeqOrdinal(height', s)
    {}

    @IsolateAssertions
    lemma SeqOrdinalConcat(height: nat, left: seq<TerminationMetric>, right: seq<TerminationMetric>)
      requires Valid()
      requires forall o <- left :: o.Valid() && height > o.height
      requires forall o <- right :: o.Valid() && height > o.height
      ensures SeqOrdinal(height, left + right) == SeqOrdinal(height, left) + SeqOrdinal(height, right)
    {
      if left == [] {
        assert left + right == right;
      } else {
        SeqOrdinalConcat(height, left[1..], right);
        assert left + right == [left[0]] + (left[1..] + right);
      }
    }

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

    lemma SeqDecreasesToProperPrefix(other: TerminationMetric, hi: nat)
      requires Valid()
      requires TMSeq?
      requires other.Valid()
      requires other.TMSeq?
      requires hi < |seqValue|
      requires seqValue[..hi] == other.seqValue
      ensures Ordinal() > other.Ordinal()
    {
      reveal Ordinal();
      var left := seqValue;
      var right := other.seqValue;
      assert left == left[..hi] + left[hi..];
      SeqOrdinalConcat(height, left[..hi], left[hi..]);
      SeqOrdinalAnyHeight(height, other.height, right);
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
      reveal Ordinal();
      var left := seqValue;
      var right := other.seqValue;
      assert left == left[..lo] + left[lo..];
      SeqOrdinalConcat(height, left[..lo], left[lo..]);
      SeqOrdinalAnyHeight(height, other.height, right);
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
      reveal Ordinal();
      var left := seqValue;
      var right := other.seqValue;
      assert left == left[..lo] + left[lo..];
      SeqOrdinalConcat(height, left[..lo], left[lo..]);
      SeqOrdinalAnyHeight(height, other.height, right);
      assert left[lo..] == left[lo..hi] + left[hi..];
      SeqOrdinalConcat(height, left[lo..hi], left[hi..]);
      SeqOrdinalConcat(height, left[..lo], left[hi..]);
    }

    ghost opaque function Ordinal(): nat 
      requires Valid()
      decreases height
      // Ensuring all ordinals are at least one makes the math much easier
      ensures Ordinal() > 0
    {
      match this {
        case TMBool(boolValue, _) => if boolValue then 2 else 1
        case TMNat(natValue, _) => natValue + 1
        case TMChar(charValue, _) => charValue + 1
        case TMSet(setValue, _) => |setValue| + 1
        case TMSeq(seqValue, _) => SeqOrdinal(height, seqValue) + 1
        case TMObject(objectValue, _) => 1
        case TMDatatype(children, _) => SeqOrdinal(height, children) + 1
      }
    }
  }
}

module TerminationExample {

  import opened Std.Termination

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

    Tuple(tm2, tm2).DecreasesTo(Tuple(tm, tm2));
    assert Tuple(tm2, tm2).Ordinal() > Tuple(tm, tm2).Ordinal();
    Tuple(tm2, tm2).DecreasesTo(Tuple(tm2, tm));
    assert Tuple(tm2, tm2).Ordinal() > Tuple(tm2, tm).Ordinal();

    // Can't be verified
    // assert (Tuple(tm, tm2).Ordinal() > Tuple(tm2, tm).Ordinal());
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

  lemma {:axiom} AddStrictlyIncreasingOnRight(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    requires right > right'
    ensures left + right > left + right'

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

  // Helpful lemmas

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
        > { AddStrictlyIncreasingOnRight(Times(base, a'), base, b); }
        Times(base, a') + b;
      }
    } else {
      calc {
        Times(base, a);
        >= { TimesStrictlyIncreasingOnRight(base, a, a' + 1); }
        Times(base, a' + 1);
        Times(base, a') + base;
        > { AddStrictlyIncreasingOnRight(Times(base, a'), base, b); }
        Times(base, a') + b;
      }
    }
  }
}
