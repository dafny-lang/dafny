// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Under the assumption that invariants can only read "this"
// and not refer to any inherited fields, invariants must at
// most and at least accommodate any this-reading predicate
// over a set of non-reference-typed fields

type A(!new)

predicate {:axiom} P(x: A)

type Subset = x : A | P(x) witness *

trait UseOfSubset {
  var x: Subset
  method Modify()
    modifies this
  {
    var oldX := x;
    x :| assume {:axiom} !P(x); // error: subset constraint not satisfied
    x := oldX;
  }
}

trait UseOfInvariant {
  var x: A
  invariant P(x)
  
  method Modify()
    modifies this
  {
    var oldX := x;
    x :| assume {:axiom} !P(x); // no problem!
    x := oldX;
  }
}