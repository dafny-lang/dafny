// RUN: %exits-with 2 %resolve --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Account {
  var credit: nat
  var debit: nat
  invariant Balance() >= 0 // NB: can't use Balance() here b/c it would be recursive
  function Balance(): nat // NB: uses the invariant to be well-defined
    reads this
  {
    assert this.invariant(); credit - debit
  }
}
