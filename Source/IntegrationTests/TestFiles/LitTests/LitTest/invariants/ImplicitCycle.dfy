// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var valid: bool
  predicate Valid()
    ensures valid
    reads this
  {
    valid
  }
  invariant Valid()
  method Falsify()
    modifies this
  {
    valid := false;
    print 1 / 0;
  }
  constructor() {
    valid := true;
  }
}
