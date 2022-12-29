// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)

lemma L()
  ensures forall y :: P(old(y))
