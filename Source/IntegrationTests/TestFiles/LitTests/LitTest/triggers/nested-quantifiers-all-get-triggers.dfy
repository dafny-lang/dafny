// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This checks that nested quantifiers do get triggers, and that the parent
// quantifier does not get annotated twice

method M() {
  ghost var x := forall s: set<int>, x: int :: (x in s ==> forall y :: y == x ==> y in s);
}
