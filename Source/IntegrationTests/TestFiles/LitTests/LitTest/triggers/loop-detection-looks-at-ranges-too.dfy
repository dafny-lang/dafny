// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that loops between the range and the term of a quantifier
// are properly detected.

ghost predicate P(x: int)

method M(x: int) {
  // This will be flagged as a loop even without looking at the range
  assert true || forall x: int | P(x) :: P(x+1);
  // This requires checking the range for looping terms
  assert true || forall x: int | P(x+1) :: P(x);
}
