// RUN: %exits-with 4 %verify --allow-axioms --resource-limit 1200 %s > %t
// RUN: %diff "%s.expect" "%t"
module Power {

  opaque function Pow(b: int, e: nat): int
    decreases e
  {
    if e == 0 then
      1
    else
      b * Pow(b, e - 1)
  }

  /* Add exponents when multiplying powers with the same base. */
  lemma LemmaPowAdds(b: int, e1: nat, e2: nat)
    decreases e1
    ensures Pow(b, e1 + e2) == Pow(b, e1) * Pow(b, e2)

  lemma LemmaPowSubAddCancel(b: int, e1: nat, e2: nat)
    decreases e1
    requires e1 >= e2
    ensures Pow(b, e1 - e2) * Pow(b, e2) == Pow(b, e1)
  {
    LemmaPowAdds(b, e1 - e2, e2);
  }

}
