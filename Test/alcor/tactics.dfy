lemma ImpIntro(a: bool, b: bool)
  requires hAB: a ==> b
  requires hA: a
{
  reveal imp_elim(hAB, hA);
  assert b;
}


// Caret below this line




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
  assert forall a, b :: (a ==> b) && a ==> (b && a); // TODO: Remove once ensures can be proven automatically
}






// Alcor-checked 80% tactical proof style, 20% declaratif
lemma Declarative1Tactic4Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    reveal
      intro(env),
      cases(env, hAB, hA),
      cases(),                    // Goal b && a is split
      imp_elim(hAB, hA),          // Solve the goal b
      intro(b),
      recall(hA);                 // Solves the goal a
    assert ((a ==> b) && a) ==> (b && a); // TODO: remove once forall can be proven automatically
  }
}






// Alcor-checked 60% tactical proof style, 40% declarative
lemma Declarative2Tactic3Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if /*env: */((a ==> b) && a) {
      reveal
        rename(h, env),
        cases(env, hAB, hA),
        cases(),                    // Goal b && a is split
        imp_elim(hAB, hA),          // Solve the goal b
        intro(hB),
        recall(hA);                 // Solves the goal a
      assert b && a;                // The ensures of the if
    }
    assert ((a ==> b) && a) ==> (b && a) by {
      reveal recall(h);
    }
  }
}

// Alcor-checked 40% tactical proof style, 60% declarative
lemma Declarative3Tactic2Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if ((a ==> b) && a) {
      reveal rename(h, env),
             cases(env, hAB, hA);
      reveal imp_elim(hAB, hA);
      assert b;
      reveal cases(h, hAB, hA),
             recall(hA);
      assert a;
      assert b && a;
    }
  }
}




// Alcor-checked 20% tactical proof style, 80% declarative
lemma Declarative4Tactic1Proof()
  ensures forall a, b :: (a ==> b) && a ==> (b && a)
{
  forall a, b ensures ((a ==> b) && a) ==> (b && a) {
    if ((a ==> b) && a) {
      assert hAB: a ==> b by {
        reveal cases(h, hAB, _), recall(hAB);
      }
      assert hA: a by {
        reveal cases(h, _, hA), recall(hA);
      }
      assert b by { reveal imp_elim(hAB, hA); }
      assert a by { reveal recall(hA); }
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








method Workaround() {
  assert true;
}
