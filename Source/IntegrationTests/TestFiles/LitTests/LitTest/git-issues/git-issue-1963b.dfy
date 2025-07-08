// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


/// This file checks that refinement is forbidden for datatypes

module A {
  datatype D = D
  lemma P(d: D) ensures d == D {}
}

module B refines A {
  datatype D = ... D | D' // Error: Cannot change (or repeat) constructors
}

method M() ensures false {
  assert B.D == B.D' by { B.P(B.D'); }
}
