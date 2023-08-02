
// Separated class
class Account {
  var money: int
  method Add(extra: int)
    modifies this
    ensures money == old(money) + extra
  {
    this.money := this.money + extra;
  }
}

// This function requires the caller to have exclusive read access over all the accounts
function Sum(s: seq<Account>): int reads s {
  if |s| == 0 then 0 else Sum(s[0..|s|-1]) + s[|s|-1].money
}

predicate readLocked(s: seq<Account>, extraRights: set<object>) {
  (set x | x in s) <= extraRights
}

// Separated but invariant is True.
class BankAccount {
  const accounts: seq<Account>
  var total: int

  predicate Invariant() {
    forall i, j | 0 <= i < j < |accounts| :: accounts[i] != accounts[j]
  }

  // Requires to hav exclusive read access over all the accounts, which is not granted usually.
  predicate GlobalInvariant() reads this, this.accounts {
    Sum(accounts[..]) == total
  }

  twostate lemma GlobalInvariantInvariant0(accounts: seq<Account>)
    requires forall k | 0 <= k < |accounts| :: accounts[k].money == old(accounts[k].money)
    ensures Sum(accounts[..]) == old(Sum(accounts[..]))
  {
    if |accounts| == 0 {
    } else {
      calc {
        Sum(accounts[..]);
        Sum(accounts[0..|accounts|-1]) + accounts[|accounts|-1].money;
        Sum(accounts[0..|accounts|-1]) + old(accounts[|accounts|-1].money);
        { GlobalInvariantInvariant0(accounts[0..|accounts|-1]); }
        old(Sum(accounts[0..|accounts|-1])) + old(accounts[|accounts|-1].money);
      }
    }
  }

  twostate lemma GlobalInvariantInvariant1(accounts: seq<Account>, i: int, money: int)
    requires 0 <= i < |accounts|
    requires accounts[i].money == old(accounts[i].money) + money
    requires forall k | 0 <= k < |accounts| && k != i :: accounts[k].money == old(accounts[k].money)
    ensures Sum(accounts[..]) == old(Sum(accounts[..])) + money
  {
    if i == |accounts|-1 {
      calc {
        Sum(accounts[..]);
        Sum(accounts[0..|accounts|-1]) + accounts[i].money;
        Sum(accounts[0..|accounts|-1]) + old(accounts[i].money) + money;
        { GlobalInvariantInvariant0(accounts[0..|accounts|-1]); }
        old(Sum(accounts[0..|accounts|-1])) + old(accounts[i].money) + money;
        old(Sum(accounts[0..|accounts|-1]) + accounts[i].money) + money;
        old(Sum(accounts[..])) + money;
      }
    } else {
      calc {
        Sum(accounts[..]);
        Sum(accounts[0..|accounts|-1]) + accounts[|accounts|-1].money;
        Sum(accounts[0..|accounts|-1]) + old(accounts[|accounts|-1].money);
        { GlobalInvariantInvariant1(accounts[0..|accounts|-1], i, money); }
        (old(Sum(accounts[0..|accounts|-1])) + money) + old(accounts[|accounts|-1].money);
        old(Sum(accounts[0..|accounts|-1])) + old(accounts[|accounts|-1].money) + money;
        old(Sum(accounts[0..|accounts|-1]) + accounts[|accounts|-1].money) + money;
        old(Sum(accounts[..])) + money;
      }
    }
  }

  twostate lemma GlobalInvariantInvariant2(accounts: seq<Account>, i: int, j: int, money: int)
    requires 0 <= i < j < |accounts|
    requires accounts[i].money == old(accounts[i].money) + money
    requires accounts[j].money == old(accounts[j].money) - money
    requires forall k | 0 <= k < |accounts| && k != i && k != j :: accounts[k].money == old(accounts[k].money)
    ensures Sum(accounts[..]) == old(Sum(accounts[..]))
  {
    if j == |accounts| - 1 {
      calc {
        Sum(accounts[..]);
        Sum(accounts[..j]) + accounts[j].money;
        { GlobalInvariantInvariant1(accounts[..j], i, money); }
        (old(Sum(accounts[..j])) + money) + accounts[j].money;
        (old(Sum(accounts[..j])) + money) + (old(accounts[j].money) - money);
        old(Sum(accounts[..j])) + old(accounts[j].money);
        old(Sum(accounts[..]));
      }
    } else {
      calc {
        Sum(accounts[..]);
        { GlobalInvariantInvariant2(accounts[..|accounts|-1], i, j, money); }
        old(Sum(accounts[..]));
      }
    }
  }

  // extraRights encode the fact that we could access the frame condition using a predicate
  // so that there might be objects at the beginning we had the right to modify
  // At the call site, if these objects are in the modifies clause, then the postcondition holds
  method Transfer(i: int, money: int, j: int, extraRights: set<object>)
    requires Invariant()
    modifies this, extraRights, if 0 <= i < |accounts| && 0 <= j < |accounts| && i != j then
       {accounts[i] as object, accounts[j]} else {}
    ensures Invariant()
    ensures readLocked(this.accounts, extraRights) && old(GlobalInvariant()) ==> GlobalInvariant()
  {
    if 0 <= i < |accounts| && 0 <= j < |accounts| && i != j {
      accounts[i].Add(money);
      accounts[j].Add(-money);
      if i < j {
        GlobalInvariantInvariant2(accounts, i, j, money);
      } else {
        assert j < i;
        GlobalInvariantInvariant2(accounts, j, i, -money);
      }
      assert readLocked(this.accounts, extraRights) && old(GlobalInvariant()) ==> GlobalInvariant();
    } else {
      assert readLocked(this.accounts, extraRights) && old(GlobalInvariant()) ==> GlobalInvariant();
    }
  }
}

/*method Test(separatedClass: SeparatedClass)
  modifies separatedClass                     // Usually not needed, since the lock is auto-acquired!
  modifies separatedClass.OtherSeparatedClass // Even less needed... but this guarantees sequentiality
  requires separatedClass.Invariant()
  requires separatedClass.otherSeparatedClass.Invariant()
{
  // Still not possible to modify fields directly because of the region rule.
  separatedClass.Add(1); // Here the region is different, the invariant is assumed.
  separatedClass.Add(2);
}*/




























