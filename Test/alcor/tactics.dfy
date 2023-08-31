lemma ImpIntro(a: bool, b: bool)
  requires hAB: a ==> b
  requires hA: a
{
  reveal imp_elim(hAB, hA);
  assert b;
}

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
  assert forall a, b :: (a ==> b) && a ==> (b && a);
}



method Workaround() {
  assert true;
}
