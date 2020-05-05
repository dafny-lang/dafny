// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Spec<U> {
  var done: bool
  var hasFailed: bool
  ghost const Repr: set<object>

  predicate Valid()
    requires done || hasFailed || (!done && !hasFailed)  // tantamount to "true"
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases this, Repr

  method DoIt() returns (u: U)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures Repr == old(Repr)
    decreases this, Repr
}

class Impl<T> extends Spec<T> {
  const tt: T
  var n: nat

  constructor (t: T) {
    tt, n := t, 0;
  }

  predicate Valid()
    requires done || hasFailed || (!done && !hasFailed)
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases this, Repr
  {
    this in Repr
  }

  method DoIt() returns (t: T)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures Repr == old(Repr)
    decreases this, Repr
  {
    if done || hasFailed {
      // nothing else to do
    } else if 0 <= n < 100 {
      // do some work
      n := n + 1;
    } else if n == 100 {
      done := true;
    } else {
      hasFailed := true;
    }
    return tt;
  }
}

class FixedImpl extends Spec<int> {
  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases this, Repr
  {
    this in Repr
  }

  method DoIt() returns (element: int)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures Repr == old(Repr)
    decreases this, Repr
}
