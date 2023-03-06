// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate P(x: int)

lemma L()
  ensures forall y :: P(old(y))
