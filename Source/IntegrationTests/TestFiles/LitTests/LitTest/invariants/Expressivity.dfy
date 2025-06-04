// RUN: %verify --type-system-refresh --verify-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Under the assumption that invariants can only read "this"
// and not refer to any inherited fields, invariants must at
// most and at lest accommodate any this-reading predicate
// over a set of non-reference-typed fields
trait Wrapper<A(!new)> extends object {
  var value: A
  predicate I() reads this
  invariant I()
  function Read(): A
    reads this
  { value }
  method Mutate() modifies this
}