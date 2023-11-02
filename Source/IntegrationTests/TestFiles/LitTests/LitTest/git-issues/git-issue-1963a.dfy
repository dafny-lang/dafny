// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


/// This file checks that refinement is forbidden for newtypes

module A {
  newtype NT = x: int | x >= 0 witness 0
  lemma P(x: NT) ensures x >= 0 {}
}

module B refines A {
  newtype NT = ... x: int | x < 0 witness -1 // Error: Change (or repeat) a newtype body
}

method M() ensures false {
  assert -1 >= 0 by { B.P(-1); }
}
