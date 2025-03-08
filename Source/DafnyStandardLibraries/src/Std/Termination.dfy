

module Std.Termination {

  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TerminationMetric =
    | TMNat(natValue: nat)
    | TMChar(charValue: nat)
    | TMSeq(seqValue: seq<TerminationMetric>)
    | TMDatatype(children: seq<TerminationMetric>)

    // TODO: All other supported kinds of Dafny values
    
    // The equivalent of "decreases first, rest".
    // Can be chained to represent "decreases a, b, c, d"
    // as TMComma(a, TMComma(b, TMComma(c, d))).
    | TMComma(first: TerminationMetric, rest: TerminationMetric)
  {
    opaque predicate DecreasesTo(other: TerminationMetric) {
      match (this, other) {
        // Simple well-ordered types
        case (TMNat(left), TMNat(right)) => left > right
        case (TMChar(left), TMChar(right)) => left > right
        // TODO: etc.
        // Other is a strict subsequence of this
        case (TMSeq(left), TMSeq(right)) =>
          || (exists i    | 0 <= i < |left|      :: left[..i] == right)
          || (exists i    | 0 < i <= |left|      :: left[i..] == right)
          || (exists i, j | 0 <= i < j <= |left| :: left[..i] + left[j..] == right)
        // This is a sequence and other is a datatype and structurally included
        // (treating a sequence as a datatype with N children)
        case (TMSeq(leftSeq), TMDatatype(_)) =>
          || other in leftSeq
        // Structural inclusion inside a datatype
        // TODO: Does other have to be a datatype too?
        case (TMDatatype(leftChildren), _) =>
          || other in leftChildren

        // TODO: other cases

        case (TMComma(leftFirst, leftRest), TMComma(rightFirst, rightRest)) =>
          if leftFirst == rightFirst then
            leftRest.DecreasesTo(rightRest)
          else
            leftFirst.DecreasesTo(rightFirst)
        case (_, TMComma(rightFirst, _)) =>
          // Treat the LHS as TMComma(this, TOP)
          this == rightFirst || this.DecreasesTo(rightFirst)

        case _ => false
      }
    }

    ghost function {:axiom} Ordinal(): ORDINAL

    // TODO: prove DecreasesTo is a well-founded ordering
    // (useful exercise and helps catch typos inconsistent with Dafny's ordering)

    predicate EqualOrDecreasesTo(other: TerminationMetric) {
      this == other || DecreasesTo(other)
    }

    // Assume a mapping exists from the DecreasesTo ordering onto the ordinals.
    // This always exists, but is complicated to define concretely
    // and technically has to be defined for a whole program.
    // It's sound to just assume it exists to convince Dafny that
    // `decreases terminationMetric.Ordinal()` is valid.
    lemma {:axiom} OrdinalDecreases(other: TerminationMetric)
      requires DecreasesTo(other)
      ensures Ordinal() > other.Ordinal()

    lemma {:axiom} DecreasesToTransitive(middle: TerminationMetric, right: TerminationMetric)
      requires 
        || (EqualOrDecreasesTo(middle) && middle.DecreasesTo(right))
        || (DecreasesTo(middle) && middle.EqualOrDecreasesTo(right))
      ensures DecreasesTo(right)

    lemma {:axiom} EqualOrDecreasesToTransitive(middle: TerminationMetric, right: TerminationMetric)
      requires EqualOrDecreasesTo(middle) && middle.EqualOrDecreasesTo(right)
      ensures EqualOrDecreasesTo(right)
  }
}
