// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var valid: bool
  lemma Call()
    ensures valid
  {
  }
  invariant (Call(); valid)
  constructor() {
    valid := true;
  }
}
