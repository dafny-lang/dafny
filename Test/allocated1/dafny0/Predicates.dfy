// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ------------------------------------------------

abstract module Loose {
  class MyNumber {
    var N: int
    ghost var Repr: set<object>
    ghost predicate Valid()
      reads this, Repr
    {
      this in Repr &&
      0 <= N &&
      CustomValid()
    }
    ghost predicate CustomValid()
      reads this, Repr
    constructor Init()
      ensures Valid() && fresh(Repr)
    {
      N, Repr := 0, {this};
      new;
      assume CustomValid();  // to be verified in refinement modules
    }

    method Inc()
      requires Valid()
      modifies Repr
      ensures old(N) < N
      ensures Valid() && fresh(Repr - old(Repr))
    {
      N := N + 2;
      assume CustomValid();
    }
    method Get() returns (n: int)
      requires Valid()
      ensures n == N
    {
      n := N;
    }
  }
}

module Tight refines Loose {
  class MyNumber ... {
    ghost predicate CustomValid...
    {
      N % 2 == 0
    }
    constructor Init()
      ensures N == 0
    method Inc()
      ensures N == old(N) + 2
  }
}

abstract module UnawareClient {
  import L = Loose
  method Main0() {
    var n := new L.MyNumber.Init();
    assert n.N == 0;  // error: this is not known
    n.Inc();
    n.Inc();
    var k := n.Get();
    assert k == 4;  // error: this is not known
  }
}

module AwareClient {
  import T = Tight
  method Main1() {
    var n := new T.MyNumber.Init();
    assert n.N == 0;
    n.Inc();
    n.Inc();
    var k := n.Get();
    assert k == 4;
  }
}

// -------- Quantifiers ----------------------------------------

module Q0 {
  class C {
    var x: int
    ghost predicate P()
      reads this
    {
      true
    }
    method M()
      modifies this
      ensures forall c: C :: c.P()  // this is the only line that's different from Test/dafn0/Predicates.dfy
    {
    }
    ghost predicate Q()
      reads this
    {
      x < 100
    }
    method N()
      modifies this
      ensures forall c: C :: c == this ==> c.Q()
    {  // error: fails to establish postcondition (but this error should not be repeated in Q1 or Q2 below)
      x := 102;
    }
    ghost predicate R()  // a body-less predicate
      reads this
  }
}

module Q1 refines Q0 {
  class C ... {
    ghost predicate R...  // no body yet
  }
}

module Q2 refines Q1 {
  class C ... {
    ghost predicate R... { x % 3 == 2 }  // finally, give it a body
  }
}
