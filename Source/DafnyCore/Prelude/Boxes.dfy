module Boxes {
  export
    provides Box, arbitrary
    provides Below, Reflexive, Antisymmetric, Transitive, Total
    reveals Less
    provides LessIrreflexive, LessAsymmetric, LessBelowAsymmetric, LessTransitive, LessBelowTransitive, Connected
    provides BelowIsNonStrictLess, NotLess

  type Box(==,0,!new)

  const arbitrary: Box

  // The following predicate and 4 lemmas postulate a total order "Below" on Box'es.

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

  lemma BelowIsNonStrictLess(a: Box, b: Box)
    ensures Below(a, b) <==> Less(a, b) || a == b
  {
    calc {
      Less(a, b) || a == b;
      (Below(a, b) && a != b) || a == b;
      Below(a, b) || a == b;
      { Reflexive(a); }
      Below(a, b);
    }
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

  lemma NotLess(a: Box, b: Box)
    ensures !Less(a, b) <==> Below(b, a)
  {
    if !Less(a, b) {
      calc {
        true;
        { Connected(a, b); }
        a == b || Less(a, b) || Less(b, a);
        // assumption !Less(a, b)
        a == b || Less(b, a);
        { BelowIsNonStrictLess(b, a); }
        Below(b, a);
      }
    }

    if Less(a, b) {
      assert !Below(b, a) by {
        if Below(b, a) {
          LessBelowAsymmetric(a, b);
          assert false;
        }
      }
    }
  }

  lemma LessTransitive(a: Box, b: Box, c: Box)
    requires Less(a, b) && Less(b, c)
    ensures Less(a, c)
  {
    LessBelowTransitive(a, b, c);
  }

  lemma LessBelowTransitive(a: Box, b: Box, c: Box)
    requires
      || (Less(a, b) && Below(b, c))
      || (Below(a, b) && Less(b, c))
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
