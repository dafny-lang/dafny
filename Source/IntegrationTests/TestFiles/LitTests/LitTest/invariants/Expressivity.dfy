// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Under the assumption that invariants can only read "this"
// and not refer to any inherited fields, invariants must at
// most and at least accommodate any this-reading predicate
// over a set of non-reference-typed fields

trait UseOfSubset extends object {
  var x: nat
  method Modify()
    modifies this
  {
    var oldX := x;
    x := -1; // error: subset constraint not satisfied
    x := oldX;
  }
}

trait UseOfInvariant extends object {
  var x: int
  invariant x >= 0
  
  method Modify()
    modifies this
  {
    var oldX := x;
    x := -1;
    x := oldX;
  }
}