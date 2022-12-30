// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This tests checks that quantifier splitting is resilient to the fact that
// certain statements (like calc) can return duplicate subexpressions. This was
// once a problem, because a quantifier that got returned twice would get split
// on the first pass over it, and would have its nely created children re-split
// on the second pass. This created a split quantifier whose children were split
// quantifiers, which violated an invariant of spliit quantifiers.

abstract module Base { }

module Blah refines Base {
  lemma A() {
    calc {
	    forall b :: b;
   	}
  }
}

