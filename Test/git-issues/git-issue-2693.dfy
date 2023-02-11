// RUN: %exits-with 4 %dafny /compile:0 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  method Test() returns (result: Result)
    ensures result.Bad? ==> result.c.IsFailure()
  {
    var c := new EvenGood_OddBad;
    c.a := 0;
    var x :- IncreaseAndReturn(c); // error: postcondition failure; deprecation warnings: PropagateFailure/Extract are methods
    assert !c.IsFailure(); // error: assertion failure
    return Good(x);
  }

  class EvenGood_OddBad {
    var a: int

    function IsFailure(): bool
      reads this
    {
      a % 2 == 1
    }

    method PropagateFailure() returns (r: Result)
      requires IsFailure()
      modifies this
    {
      a := 0;
      return Bad(this);
    }

    method Extract() returns (x: int)
      requires !IsFailure()
      modifies this
    {
      x := a;
      a := 19;
    }
  }

  datatype Result = Good(x: int) | Bad(c: EvenGood_OddBad)

  method IncreaseAndReturn(c: EvenGood_OddBad) returns (r: EvenGood_OddBad)
    modifies c
    ensures old(c.a) <= c.a && r == c
  {
    var n: nat;
    c.a := c.a + n;
    return c;
  }
}

module B {
  // This module gives two examples of failure-compatible types where members
  // are ghost in useful ways (well, not very useful here, but at least they
  // make sense to call them legal code).

  datatype GhostFailureCompatible = Success | Failure
  {
    ghost predicate IsFailure()
    ghost function PropagateFailure(): GhostFailureCompatible
    ghost function Extract(): int
  }

  datatype GhostFailureCompatible' = Success' | Failure'
  {
    ghost predicate IsFailure()
    ghost function PropagateFailure(): GhostFailureCompatible'
  }

  ghost method Client() returns (r: GhostFailureCompatible) {
    var e: GhostFailureCompatible;
    var x :- e;
  }

  ghost method Client'() returns (r: GhostFailureCompatible') {
    var e: GhostFailureCompatible';
    :- e;
  }
}
