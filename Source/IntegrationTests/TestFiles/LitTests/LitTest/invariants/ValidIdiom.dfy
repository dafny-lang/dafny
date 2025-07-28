// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Nat {
  var value: int
  function Value(): nat
    reads this
  {
    assert this.invariant(); value // OK, this !in open
  }
  predicate Valid()
    reads this
  {
    //assert this.invariant(); // NOT OK! function doesn't terminate
    value >= 0 // OK: this !in open, but does not use this.invariant()
  }
  invariant Valid()
}