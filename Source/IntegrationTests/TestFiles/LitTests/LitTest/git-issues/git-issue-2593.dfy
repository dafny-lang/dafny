// RUN: %testDafnyForEachResolver "%s" -- --allow-warnings


ghost predicate P(x: int)

lemma L()
  ensures forall y :: P(old(y))
