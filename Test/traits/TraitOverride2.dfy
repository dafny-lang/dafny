// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Spec<U> {
  var done: bool
  var hasFailed: bool
  ghost const Repr: set<object>

  ghost predicate Valid()
    requires done || hasFailed || (!done && !hasFailed)  // tantamount to "true"
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr

  method DoIt() returns (u: U)
    requires Valid()
    modifies Repr
    ensures Valid()
    decreases Repr
}

class Impl<T> extends Spec<T> {
  const tt: T
  var n: nat

  constructor (t: T)
    ensures Valid()
  {
    tt, n := t, 0;
    Repr := {this};
    new;
    assert this in Repr;
  }

  ghost predicate Valid()
    requires done || hasFailed || (!done && !hasFailed)
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr
  {
    this in Repr
  }

  method DoIt() returns (t: T)
    requires Valid()
    modifies Repr
    ensures Valid()
    decreases Repr
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

class AnotherImpl<T> extends Spec<seq<T>> {
  constructor ()
    ensures Valid()
  {
    Repr := {this};
    new;
    assert this in Repr;  // this had once failed
  }

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr
  { this in Repr }

  method DoIt() returns (u: seq<T>)
    requires Valid()
    modifies Repr
    ensures Valid()
    decreases Repr
  { }
}

class FixedImpl extends Spec<int> {
  constructor (arr: array<real>)
    ensures Valid()
  {
    Repr := {this, arr};
  }

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr
  {
    this in Repr
  }

  method DoIt() returns (element: int)
    requires Valid()
    modifies Repr
    ensures Valid()
    decreases Repr
}
