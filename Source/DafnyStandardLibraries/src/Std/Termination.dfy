

module Std.Termination {

  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TerminationMetric =
    | TMTop
    | TMBool(boolValue: bool)
    | TMNat(natValue: nat)
    | TMChar(charValue: nat)
    // No ordering on objects themselves, but commonly used in Repr set<object> values
    | TMObject(objectValue: object)
    | TMSeq(seqValue: seq<TerminationMetric>)
    | TMSet(setValue: set<TerminationMetric>)
    | TMDatatype(children: seq<TerminationMetric>)

      // Other kinds of Dafny values are valid here too,
      // and may be added in the future.

      // The equivalent of "decreases first, rest".
      // Can be chained to represent "decreases a, b, c, d"
      // as TMComma(a, TMComma(b, TMComma(c, d))).
    | TMComma(first: TerminationMetric, rest: TerminationMetric)
  {
    opaque predicate DecreasesTo(other: TerminationMetric) {
      match (this, other) {
        case (TMTop, _) => !other.TMTop?

        // Simple well-ordered types
        case (TMBool(left), TMBool(right)) => left && !right
        case (TMNat(left), TMNat(right)) => left > right
        case (TMChar(left), TMChar(right)) => left > right
        case (TMSet(left), TMSet(right)) => left > right
        // Other is a strict subsequence of this
        case (TMSeq(left), TMSeq(right)) =>
          || (exists i    | 0 <= i < |left|      :: left[..i] == right)
          || (exists i    | 0 < i <= |left|      :: left[i..] == right)
          || (exists i, j | 0 <= i < j <= |left| :: left[..i] + left[j..] == right)
        // This is a sequence and other is structurally included
        // (treating a sequence as a datatype with N children)
        case (TMSeq(leftSeq), _) =>
          || other in leftSeq
        // Structural inclusion inside a datatype
        case (TMDatatype(leftChildren), _) =>
          || other in leftChildren

        case (TMComma(leftFirst, leftRest), _) =>
          || (other.TMComma? && (
            || leftFirst.DecreasesTo(other.first)
            || (leftFirst == other.first && leftRest.DecreasesTo(other.rest))))
          // TODO: Not a rule Dafny itself applies, but seems safe?
          || leftFirst == other
          || leftRest == other

        case _ => false
      }
    }

    predicate NonIncreasesTo(other: TerminationMetric) {
      this == other || DecreasesTo(other)
    }

    // Assume a mapping exists from the DecreasesTo ordering onto the ordinals.
    // This always exists, but is complicated to define concretely
    // and technically has to be defined for a whole program.
    // It's sound to just assume it exists to convince Dafny that
    // `decreases terminationMetric.Ordinal()` is valid.
    ghost function {:axiom} Ordinal(): ORDINAL
    lemma {:axiom} OrdinalDecreases(other: TerminationMetric)
      requires DecreasesTo(other)
      ensures Ordinal() > other.Ordinal()

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
