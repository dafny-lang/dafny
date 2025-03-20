

module Std.Termination {

  import opened Collections.Set

  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TerminationMetric =
    // | TMTop
    | TMBool(boolValue: bool, height: nat)
    | TMNat(natValue: nat, height: nat)
    | TMChar(charValue: nat, height: nat)
    //   // No ordering on objects themselves, but commonly used in Repr set<object> values
    // | TMObject(objectValue: object)
    // | TMSeq(seqValue: seq<TerminationMetric>)
    | TMSet(setValue: set<TerminationMetric>, height: nat)
    // | TMDatatype(children: seq<TerminationMetric>)

    //   // Other kinds of Dafny values are valid here too,
    //   // and may be added in the future.

    //   // The equivalent of "decreases first, rest".
    //   // Can be chained to represent "decreases a, b, c, d"
    //   // as TMComma(a, TMComma(b, TMComma(c, d))).
    // | TMComma(first: TerminationMetric, rest: TerminationMetric)
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

    // ghost function SetSubtractOne(tm: TerminationMetric): (result: TerminationMetric)
    //   requires TMSet?
    //   requires Valid()
    //   requires tm in setValue
    //   ensures result.Valid()
    //   ensures result.TMSet?
    //   ensures result.setValue == setValue - {tm}
    // {
    //   var restSetValue := setValue - {tm};
    //   var rest := TMSet(restSetValue, height - tm.height - 1);
    //   assert height > SetHeightSum(setValue);
    //   assert height - tm.height - 1 > SetHeightSum(restSetValue);
    //   assert rest.Valid();
    //   rest
    // }

    opaque predicate DecreasesTo(other: TerminationMetric) {
      match (this, other) {
        // case (TMTop, _) => !other.TMTop?

        case (TMBool(left, _), TMBool(right, _)) => left && !right
        case (TMNat(left, _), TMNat(right, _)) => left > right
        case (TMChar(left, _), TMChar(right, _)) => left > right
        case (TMSet(left, _), TMSet(right, _)) => left > right
        // // Other is a strict subsequence of this
        // case (TMSeq(left), TMSeq(right)) =>
        //   || (exists i    | 0 <= i < |left|      :: left[..i] == right)
        //   || (exists i    | 0 < i <= |left|      :: left[i..] == right)
        //   || (exists i, j | 0 <= i < j <= |left| :: left[..i] + left[j..] == right)
        // // This is a sequence and other is structurally included
        // // (treating a sequence as a datatype with N children)
        // case (TMSeq(leftSeq), _) =>
        //   || other in leftSeq
        // // Structural inclusion inside a datatype
        // case (TMDatatype(leftChildren), _) =>
        //   || other in leftChildren

        // case (TMComma(leftFirst, leftRest), _) =>
        //   // Lexicographic ordering
        //   || (other.TMComma? && (
        //         || leftFirst.DecreasesTo(other.first)
        //         || (leftFirst == other.first && leftRest.DecreasesTo(other.rest))))
        //   || leftFirst == other || leftFirst.DecreasesTo(other)
        //   // TODO: UNSOUND, remove and find a workaround
        //   || leftRest == other || leftRest.DecreasesTo(other)

        case _ => false
      }
    }

    predicate NonIncreasesTo(other: TerminationMetric) {
      this == other || DecreasesTo(other)
    }

    ghost function Ordinal(): ORDINAL 
      requires Valid()
      decreases height
    {
      match this {
        case TMBool(boolValue, _) => if boolValue then 1 else 0
        case TMNat(natValue, _) => natValue as ORDINAL
        case TMChar(charValue, _) => charValue as ORDINAL
        case TMSet(setValue, _) => |setValue| as ORDINAL
      }
    }

    ghost function SetOrdinalSum(): ORDINAL
      requires Valid()
      requires TMSet?
      decreases height, 0
    {
      if setValue == {} then
        0
      else
        var o := ExtractFromNonEmptySet(setValue);
        var restSetValue := setValue - {o};
        var rest := TMSet(restSetValue, height - o.height - 1);
        1 + o.Ordinal() + rest.SetOrdinalSum()
    }

    ghost function {:axiom} Omega(): ORDINAL 
      ensures !Omega().IsNat
      ensures Omega().IsLimit
      ensures forall other: ORDINAL | other.IsLimit && other != 0 :: Omega() <= other

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
