// All the proofs of this file should be 100% checked by Alcor without having to rely on Z3.

// Alcor-checked 100% tactical proof style
lemma Declarative0Tactic5Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  reveal
    intro(a),
    intro(b),
    intro(env),
    cases(env, hAB, hA),
    cases(),
    imp_elim(hAB, hA),
    intro(b),
    recall(hA);
}


// Alcor-checked 80% tactical proof style, 20% declaratif
lemma Declarative1Tactic4Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    reveal
      imp_elim(env),
      cases(env, hAB, hA),
      cases(),              // Goal b && a is split
      imp_elim(hAB, hA),          // Solve the goal b
      hA;                         // Solves the goal a
  }
}

// Alcor-checked 60% tactical proof style, 40% declarative
lemma Declarative2Tactic3Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if env: ((a ==> b) && a) {
      reveal
        cases(env, hAB, hA),
        cases(),                    // Goal b && a is split
        imp_elim(hAB, hA),          // Solve the goal b
        hA;                         // Solves the goal a
      assert b && a;                // The ensures of the if
    }
  }
}

// Alcor-checked 40% tactical proof style, 60% declarative
lemma Declarative3Tactic2Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if env: ((a ==> b) && a) {
      reveal cases(env, hAB, hA);
      assert b by {
        reveal imp_elim(hAB, hA);
      }
      assert a by {
        reveal hA;
      }
      assert b && a;
    }
  }
}

lemma Declarative4Tactic1Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if env: ((a ==> b) && a) {
      assert hAB: a ==> b;
      assert hA: a;
      assert b by {
        assert a ==> b by hAB;
        assert a by hA;
      }
      assert a by hA;
      assert b && a;
    }
  }
}

// Alcor-checked 100% declarative proof style
lemma Declarative5Tactic0Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if ((a ==> b) && a) {
      assert a;       // Obtain a by AndElimRight
      assert (a ==> b) && a; // Recall (a ==> b) && a
      assert a ==> b; // Obtain a ==> b by AndElimLeft
      assert a;       // Recall a
      assert b;       // Obtain b by ImpElim
      assert b && a;  // AndIntro
    }
  }
}

// Alcor-checked 80% declarative proof style, 20% procedural
lemma Declarative4Procedural1Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if env: ((a ==> b) && a) {
      assert hAB: a ==> b by AndElimLeft(env);
      assert hA: a by AndElimRight(env);
      assert hB: b by ImpElim(hAB, hA);
      assert b && a by AndIntro(hA, hB);
    }
  }
}
// Alcor-checked 60% declarative proof style, 40% procedural
lemma Declarative3Procedural2Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if env: ((a ==> b) && a) {
      assert b && a by
        var hAB := AndElimLeft(env);
        var hA := AndElimRight(env);
        var hB := ImpElim(hAB, hA);
        AndIntro(hB, hA);
    }
  }
}

// Alcor-checked 40% declarative proof style, 60% procedural
lemma Declarative2Procedural3Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    assert ((a ==> b) && a) ==> b && a by
      ImpIntro(``(a ==> b) && a``, (env: Proof) =>
        var hAB := AndElimLeft(env);
        var hA := AndElimRight(env);
        var hB := ImpElim(hAB, hA);
        AndIntro(hB, hA);
     );
  }
}

// Alcor-checked 20% declarative proof style, 80% procedural
lemma Declarative1Procedural4Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) by
    ImpIntro(``(a ==> b) && a``, (env: Proof) =>
      var hAB := AndElimLeft(env);
      var hA := AndElimRight(env);
      var hB := ImpElim(hAB, hA);
      AndIntro(hB, hA);
    );
}

// Alcor-checked 100% procedural proof style
lemma Declarative0Procedural5Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
    by
    forallIntro(a,
      forallIntro(b,
        ImpIntro(``(a ==> b) && a``, (env: Proof) =>
          var hAB := AndLeft(env);
          var hA := AndRight(env);
          var hB := ImpElim(hAB, hA);
          AndIntro(hB, hA))))
{}