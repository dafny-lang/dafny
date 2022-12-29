// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file contains tests for messags about various deprecated features.
// As those features go away completely, so can the corresponding tests.

method Main() {
  // Test that we get all the way to compilation, despite the deprecation warnings below
  print "yet here we are\n";
}

// ----------

class C {
  constructor ()
    modifies this  // deprecation warning: "this" is no longer needed in modifies of a constructor
  {
  }
}

// ----------

inductive predicate InductivePredicate()  // deprecation warning: "inductive predicate" has been renamed to "least predicate"
{ true }

copredicate CoPredicate()  // deprecation warning: "copredicate" has been renamed to "greatest predicate"
{ true }

inductive lemma InductiveLemma()  // deprecation warning: "inductive lemma" has been renamed to "least lemma"
{ }

colemma CoLemma()  // deprecation warning: "colemma" has been renamed to "greatest lemma"
{ }

