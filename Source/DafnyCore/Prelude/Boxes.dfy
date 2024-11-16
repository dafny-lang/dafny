module Boxes {
  export
    provides Box, arbitrary
    provides Below, Reflexive, Antisymmetric, Transitive, Total
    reveals Less
    provides LessIrreflexive, LessAsymmetric, LessBelowAsymmetric, LessTransitive, Connected

  type Box(==,0,!new)

  const arbitrary: Box

  /// The following predicate and 4 lemmas postulate a total order "Below" on Box'es.

  predicate {:axiom} Below(a: Box, b: Box)

  lemma {:axiom} Reflexive(a: Box)
    ensures Below(a, a)

  lemma {:axiom} Antisymmetric(a: Box, b: Box)
    requires Below(a, b) && Below(b, a)
    ensures a == b

  lemma {:axiom} Transitive(a: Box, b: Box, c: Box)
    requires Below(a, b) && Below(b, c)
    ensures Below(a, c)

  lemma {:axiom} Total(a: Box, b: Box)
    ensures Below(a, b) || Below(b, a)

  // strict order

  predicate Less(a: Box, b: Box) {
    Below(a, b) && a != b
  }

  lemma LessIrreflexive(a: Box)
    ensures !Less(a, a)
  {
  }

  lemma LessAsymmetric(a: Box, b: Box)
    requires Less(a, b) && Less(b, a)
    ensures false
  {
    Antisymmetric(a, b);
  }

  lemma LessBelowAsymmetric(a: Box, b: Box)
    requires Less(a, b) && Below(b, a)
    ensures false
  {
    Antisymmetric(a, b);
  }

  lemma LessTransitive(a: Box, b: Box, c: Box)
    requires Less(a, b) && Less(b, c)
    ensures Less(a, c)
  {
    assert Below(a, c) by {
      Transitive(a, b, c);
    }
    assert a != c by {
      if a == c {
        Antisymmetric(a, b);
        assert a == b;
        assert false;
      }
    }
  }

  lemma Connected(a: Box, b: Box)
    ensures a != b ==> Less(a, b) || Less(b, a)
  {
    Total(a, b);
  }
}
