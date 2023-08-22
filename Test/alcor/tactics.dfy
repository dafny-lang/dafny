lemma ImpIntro(a: bool, b: bool)
  requires hAB: a ==> b
  requires hA: a
{
  reveal imp_elim(hAB, hA),
         cases(h1, h2, h3);
}

method Workaround() {
  assert true;
}
