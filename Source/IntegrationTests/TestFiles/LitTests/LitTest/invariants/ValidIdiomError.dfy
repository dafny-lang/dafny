// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Nat {
  var value: int
  function Value(): nat
    reads this
  {
    value
  }
  predicate Valid()
    reads this
  {
    assert value >= 0; value >= 0
  }
  invariant Valid()
}