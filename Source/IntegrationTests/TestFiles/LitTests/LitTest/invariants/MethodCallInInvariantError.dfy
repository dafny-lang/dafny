// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Account {
  var credit: nat
  var debit: nat
  lemma Call()
    ensures this.invariant()
  {
  }
  invariant (Call(); credit - debit >= 0)
  constructor() {
    credit := 0;
    debit := 0;
  }
}
