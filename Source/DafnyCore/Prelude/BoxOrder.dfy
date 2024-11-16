module Order {
  import Boxes

  /// This module postulates a total order "Below" on Box'es.

  predicate {:axiom} Below(a: Boxes.Box, b: Boxes.Box)

  lemma {:axiom} Reflexive(a: Boxes.Box)
    ensures Below(a, a)

  lemma {:axiom} Transitive(a: Boxes.Box, b: Boxes.Box, c: Boxes.Box)
    requires Below(a, b) && Below(b, c)
    ensures Below(a, c)

  lemma {:axiom} Antisymmetric(a: Boxes.Box, b: Boxes.Box)
    requires Below(a, b) && Below(b, a)
    ensures a == b

  lemma {:axiom} Total(a: Boxes.Box, b: Boxes.Box)
    ensures Below(a, b) || Below(b, a)

  // strict order

  predicate Less(a: Boxes.Box, b: Boxes.Box) {
    Below(a, b) && a != b
  }

  lemma LessIrreflexive(a: Boxes.Box)
    ensures !Less(a, a)
  {
  }

  lemma LessAsymmetric(a: Boxes.Box, b: Boxes.Box)
    requires Less(a, b) && Less(b, a)
    ensures false
  {
    Antisymmetric(a, b);
  }

  lemma LessBelowAsymmetric(a: Boxes.Box, b: Boxes.Box)
    requires Less(a, b) && Below(b, a)
    ensures false
  {
    Antisymmetric(a, b);
  }

  lemma LessTransitive(a: Boxes.Box, b: Boxes.Box, c: Boxes.Box)
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

  lemma Connected(a: Boxes.Box, b: Boxes.Box)
    ensures a != b ==> Less(a, b) || Less(b, a)
  {
    Total(a, b);
  }
}
