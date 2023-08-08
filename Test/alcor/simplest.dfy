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
      assert a;       // Recall a
      assert b && a;  // AndIntro
    }
  }
}

lemma Chaining2(a: bool, b: bool)
  requires a ==> b
  requires a
  ensures b
{
}
lemma Chaining(a: bool, b: bool)
  ensures b
{
  assert a ==> b; // Try to prove that true ==> (a ==> b) and then assume 
  assert a;
  assert b; // Try to prove that 
}

lemma Chaining3()
  ensures forall a: bool, b: bool :: ((a ==> b) && a) ==> b
{
  /*v_intro(a);
  v_intro(b);
  imp_intro(h);
  h1 := and_left(h);
  h2 := and_right(a);
  imp_elim(h1, h2);*/
}

lemma Chaining4()
  ensures forall a: bool, b: bool :: ((a ==> b) && a) ==> b
{
  /*forall a, b ensures ((a ==> b) && a) ==> b {
    if ((a ==> b) && a) {
      assert a ==> b; // Need of visualization
      assert (a ==> b) && a;
      assert a;
      assert a ==> b;
      assert b;
    }
    assert ((a ==> b) && a) ==> b;
  }
  v_intro(a);
  v_intro(b);
  imp_intro(h);
  h1 := and_left(h);
  h2 := and_right(a);
  imp_elim(h1, h2);*/
}


lemma Simplest(b: bool) {
  assert b ==> b;
}
lemma Simplest2(a: bool, b: bool)
{
  //assert a && b ==> b;
  assert a && b;
  assert a;
  assert a && b;
  assert b;
  assert a;
  assert b && a; 
}
