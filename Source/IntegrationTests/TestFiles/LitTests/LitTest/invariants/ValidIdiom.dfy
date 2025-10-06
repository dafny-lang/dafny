// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Nat {
  var value: int
  function Value(): int
    reads this
  {
    value
  }
  predicate Valid()
    reads this
  {
    Value() >= 0
  }
  invariant Valid()
  constructor() { value := 0; }
}