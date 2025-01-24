

module Std.Termination {

  datatype ClauseTail = More(next: TerminationMetric) | Top

  datatype TerminationMetric = TerminationMetric(first: TMValue, rest: ClauseTail) {
    predicate DecreasesTo(other: TerminationMetric) {
      if first == other.first then
        match (rest, other.rest) {
          case (_, Top) => false
          case (Top, More(_)) => true
          case (More(next), More(otherNext)) => next.DecreasesTo(otherNext)
        }
      else
        first.DecreasesTo(other.first)
    }

    ghost function {:axiom} Ordinal(): ORDINAL
  }

  // Convenience constructors
  function TerminationMetric1(value1: TMValue): TerminationMetric {
    TerminationMetric(value1, Top)
  }
  function TerminationMetric2(value1: TMValue, value2: TMValue): TerminationMetric {
    TerminationMetric(value1, More(TerminationMetric(value2, Top)))
  }
  function NatTerminationMetric(m: nat): TerminationMetric {
    TerminationMetric1(TMNat(m))
  }

  // Heterogeneous encoding of the essential features of individual
  // decreases clause list elements.
  datatype TMValue =
    | TMNat(natValue: nat)
    | TMChar(charValue: nat)
    | TMSeq(seqValue: seq<TMValue>)
    | TMDatatype(children: seq<TMValue>)
  // TODO: All other supported kinds of Dafny values
  {
    predicate DecreasesTo(other: TMValue) {
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
        case _ => false
      }
    }
  }

  // TODO: prove DecreasesTo is a well-founded ordering
  // (useful exercise and helps catch typos inconsistent with Dafny's ordering)

  // Assume a mapping exists from the DecreasesTo ordering onto the ordinals.
  // This always exists, but is complicated to define concretely
  // and technically has to be defined for a whole program.
  // It's sound to just assume it exists to convince Dafny that
  // `decreases terminationMetric.Ordinal()` is valid.
  lemma {:axiom} OrdinalOrdered(left: TerminationMetric, right: TerminationMetric)
    requires left.DecreasesTo(right)
    ensures left.Ordinal() > right.Ordinal()
}

module Example {

  datatype Tree<T> = Node(children: seq<Tree<T>>) | Nil

  function Count<T>(t: Tree<T>): nat {
    match t
    case Node(children) =>
      // assert t decreases to children;
      CountSum(children)
    case Nil =>
      0
  }

  function CountSum<T>(children: seq<Tree<T>>): nat {
    if |children| == 0 then
      0
    else
      // assert children decreases to children[0];
      var firstCount := Count(children[0]);
      // assert children decreases to children[1..];
      var restCount := CountSum(children[1..]);
      firstCount + restCount
  }
}