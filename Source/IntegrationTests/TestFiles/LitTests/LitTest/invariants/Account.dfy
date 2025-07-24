// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Account {
  var credit: nat
  var debit: nat
  // NB: can't use Balance() here b/c it would be recursive
  invariant credit - debit >= 0
  function Balance(): nat
    reads this
  {
    // NB: uses the invariant to be well-defined
    assert this.invariant(); credit - debit
  }
  method Withdraw(amount: nat)
    requires Balance() - amount >= 0
    ensures Balance() == old(Balance()) - amount // NB: this uses the invariant to be well-defined
    modifies this
  {
    debit := debit + amount;
  }
  method Deposit(amount: nat)
    ensures Balance() == old(Balance()) + amount
    modifies this
  {
    credit := credit + amount;
  }
}

method Use(a: Account)
  modifies a
{
  a.Deposit(100) by { assert a.invariant(); } // need this for the following call to be well-formed
  a.Withdraw(50);
  a.Withdraw(50);
  assert a.Balance() >= 0;
}
