// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Nat {
  var value: int
  function Value(): nat
    reads this
  {
    value // OK, this !in open
  }
  invariant Valid(this)
  static predicate Valid(self: Nat) reads self {
    self.value >= 0
  }
}