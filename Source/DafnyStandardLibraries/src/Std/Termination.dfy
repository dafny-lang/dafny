

module Std.Termination {

  import opened Collections.Set
  import opened Ordinal

  datatype LexicographicTuple = LexicographicTuple(first: TerminationMetric, second: TerminationMetric) {
    ghost predicate Valid() {
      first.Valid() && second.Valid()
    }

    opaque predicate DecreasesTo(other: LexicographicTuple) {
      || first.DecreasesTo(other.first)
      || (first == other.first && second.DecreasesTo(other.second))
    }

    ghost function Ordinal(): ORDINAL 
      requires Valid()
    {
      // Using omega + 1 as the base since we use omega for TMTop
      Times(Omega() + 1, first.Ordinal()) + second.Ordinal()
    }

    @ResourceLimit("0")
    lemma OrdinalDecreases(other: LexicographicTuple)
      requires Valid()
      requires other.Valid()
      requires DecreasesTo(other)
      ensures Ordinal() > other.Ordinal()
    {
      reveal DecreasesTo();
      reveal TerminationMetric.DecreasesTo();
      if first == other.first {
        var term := Times(Omega() + 1, first.Ordinal());
        TimesStrictlyIncreasingOnRight(Omega(), first.Ordinal(), 0);
        second.OrdinalDecreases(other.second);
        AddStrictlyIncreasingOnRight(term, second.Ordinal(), other.second.Ordinal());
      } else {
        first.OrdinalDecreases(other.first);
        TimesStrictlyIncreasingOnRight(Omega(), first.Ordinal(), other.first.Ordinal());
        RadixDecreases(Omega() + 1, first.Ordinal(), other.first.Ordinal(), other.second.Ordinal());
      }
    }
  }

  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TerminationMetric =
    | TMTop(height: nat)
    | TMBool(boolValue: bool, height: nat)
    | TMNat(natValue: nat, height: nat)
    | TMChar(charValue: nat, height: nat)
    // No ordering on objects themselves, but commonly used in Repr set<object> values
    | TMObject(objectValue: object, height: nat)
    // | TMSeq(seqValue: seq<TerminationMetric>)
    | TMSet(setValue: set<TerminationMetric>, height: nat)
    // | TMDatatype(children: seq<TerminationMetric>, height: nat)

    // Other kinds of Dafny values are valid here too,
    // and may be added in the future.
  {
    ghost predicate Valid() {
      match this {
        case TMSet(setValue, height) =>
          && (forall tm <- setValue :: tm.Valid())
          && height > SetHeightSum(setValue)
        case _ => true
      }
    }

    static ghost function SetHeightSum(s: set<TerminationMetric>): nat
      ensures forall o <- s :: SetHeightSum(s) > o.height
    {
      if s == {} then
        0
      else
        var o := ExtractFromNonEmptySet(s);
        o.height + 1 + SetHeightSum(s - {o})
    }

    opaque predicate DecreasesTo(other: TerminationMetric) 
      ensures DecreasesTo(other) ==> this != other
    {
      match (this, other) {
        case (TMTop(_), _) => !other.TMTop?
        case (TMBool(left, _), TMBool(right, _)) => left && !right
        case (TMNat(left, _), TMNat(right, _)) => left > right
        case (TMChar(left, _), TMChar(right, _)) => left > right
        case (TMSet(left, _), TMSet(right, _)) => left > right
        // Other is a strict subsequence of this
        // case (TMSeq(left), TMSeq(right)) =>
        //   || (exists i    | 0 <= i < |left|      :: left[..i] == right)
        //   || (exists i    | 0 < i <= |left|      :: left[i..] == right)
        //   || (exists i, j | 0 <= i < j <= |left| :: left[..i] + left[j..] == right)
        // // This is a sequence and other is structurally included
        // // (treating a sequence as a datatype with N children)
        // case (TMSeq(leftSeq), _) =>
        //   || other in leftSeq
        // Structural inclusion inside a datatype
        // case (TMDatatype(leftChildren, _), _) =>
        //   || other in leftChildren

        case _ => false
      }
    }

    predicate NonIncreasesTo(other: TerminationMetric) {
      this == other || DecreasesTo(other)
    }

    ghost function Ordinal(): ORDINAL 
      requires Valid()
      decreases height
      // This makes the math much easier
      ensures Ordinal() > 0
      ensures Ordinal() < Omega() + 1
      ensures TMTop? <==> Ordinal() == Omega()
    {
      match this {
        case TMTop(_) => Omega()
        case TMBool(boolValue, _) => if boolValue then 2 as ORDINAL else 1 as ORDINAL
        case TMNat(natValue, _) => natValue as ORDINAL + 1
        case TMChar(charValue, _) => charValue as ORDINAL + 1
        case TMSet(setValue, _) => |setValue| as ORDINAL + 1
        case TMObject(objectValue, _) => 1
      }
    }

    @ResourceLimit("0")
    lemma OrdinalDecreases(other: TerminationMetric)
      requires Valid()
      requires other.Valid()
      requires DecreasesTo(other)
      ensures Ordinal() > other.Ordinal()
    {
      reveal DecreasesTo();
      match (this, other) {
        case (TMSet(left, _), TMSet(right, _)) => {
          LemmaSubsetSize(right, left);
        }
        case _ => {}
      }
    }

    lemma {:axiom} DecreasesToTransitive(middle: TerminationMetric, right: TerminationMetric)
      requires
        || (NonIncreasesTo(middle) && middle.DecreasesTo(right))
        || (DecreasesTo(middle) && middle.NonIncreasesTo(right))
      ensures DecreasesTo(right)

    lemma {:axiom} NonIncreasesToTransitive(middle: TerminationMetric, right: TerminationMetric)
      requires NonIncreasesTo(middle) && middle.NonIncreasesTo(right)
      ensures NonIncreasesTo(right)
  }
}
  
module Std.Ordinal {
  ghost function {:axiom} Omega(): ORDINAL 
      ensures !Omega().IsNat
      ensures Omega().IsLimit
      ensures forall other: ORDINAL | other.IsLimit && other != 0 :: Omega() <= other

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

  // Additional axioms about addition

  // TODO: Surprised this one was necessary
  lemma {:axiom} Succ(a: ORDINAL, b: ORDINAL) 
    requires a > b
    ensures a >= b + 1

  lemma {:axiom} AddStrictlyIncreasingOnRight(left: ORDINAL, right: ORDINAL, right': ORDINAL)
    requires right > right'
    ensures left + right > left + right'

  // Multiplication

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
}
