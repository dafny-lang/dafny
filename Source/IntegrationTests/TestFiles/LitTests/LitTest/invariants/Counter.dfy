// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Store the old(value) since we don't yet have twostate invariants
class Counter {
  ghost var old_value: nat
  ghost var value: nat
  constructor() {
    old_value := 0;
    value     := 0;
  }
  method Increment()
    modifies this
  {
    old_value := value;
    value     := value + 2;
  }
  invariant old_value == value || value == old_value + 1
}

