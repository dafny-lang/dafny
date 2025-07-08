// RUN: %diff "%s" "%s"
lemma {:axiom} BadAssumptionButWeDon'tCare(x: int)
  ensures x*x == 2
