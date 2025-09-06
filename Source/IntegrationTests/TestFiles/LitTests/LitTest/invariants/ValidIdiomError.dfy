// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The apparent circularity between Valid() and the invariant isn't explicitly caught, but
// Value(), as written, isn't well-formed (value isn't a nat). If this.invariant() is 
// asserted in the boy of Value(), then this error converts to a non-termination error

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
    Value() >= 0
  }
  invariant Valid()
  constructor() { value := 0; }
}