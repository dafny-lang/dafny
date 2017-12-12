// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class C {
    var x: int;
    protected predicate P()
      reads this;
    {
      x < 100
    }
    method M()
      modifies this;
      ensures P();
    {
      x := 28;
    }
    method N()
      modifies this;
      ensures P();
    {  // error: in module B, the postcondition P() has been strengthened and no longer holds
      x := -28;
    }
  }
}

module B refines A {
  class C {
    protected predicate P()
    {
      0 <= x
    }
  }
}

// ------------------------------------------------

module Loose {
  class MyNumber {
    var N: int;
    ghost var Repr: set<object>;
    protected predicate Valid()
      reads this, Repr;
    {
      this in Repr &&
      0 <= N
    }
    constructor Init()
      ensures Valid() && fresh(Repr - {this});
    {
      N, Repr := 0, {this};
    }
    
    method Inc()
      requires Valid();
      modifies Repr;
      ensures old(N) < N;
      ensures Valid() && fresh(Repr - old(Repr));
    {
      N := N + 2;
    }
    method Get() returns (n: int)
      requires Valid();
      ensures n == N;
    {
      n := N;
    }
  }
}

module Tight refines Loose {
  class MyNumber {
    protected predicate Valid()
    {
      N % 2 == 0
    }
    constructor Init()
      ensures N == 0;
    method Inc()
      ensures N == old(N) + 2;
  }
}

module UnawareClient {
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

// -------- Tricky refinement inheritance ----------------------------------------

module Tricky_Base {
  class Tree {
    var x: int;
    predicate Constrained()
      reads this;
    {
      x < 10
    }
    protected predicate Valid()
      reads this;
    {
      x < 100
    }
    method Init()
      modifies this;
      ensures Valid();
    {  // error: in module Tricky_Full, the strengthened postcondition Valid() no longer holds
      x := 20;
    }
  }
}

module Tricky_Full refines Tricky_Base {
  class Tree {
    protected predicate Valid()
    {
      Constrained()  // this causes an error to be generated for the inherited Init
    }
  }
}

// -------- Quantifiers ----------------------------------------

module Q0 {
  class C {
    var x: int;
    protected predicate P()
      reads this;
    {
      true
    }
    method M()
      modifies this;
      ensures forall c: C :: allocated(c) ==> c.P();
    {  // error: in module Q1, the postcondition no longer holds
    }
    predicate Q()
      reads this;
    {
      x < 100
    }
    method N()
      modifies this;
      ensures forall c: C :: c == this ==> c.Q();
    {  // error: fails to establish postcondition (but this error should not be repeated in Q1 below)
      x := 102;
    }
    predicate R() reads this;  // a body-less predicate
  }
}

module Q1 refines Q0 {
  class C {
    protected predicate P()
    {
      x == 18
    }
    predicate R()  // no body yet
  }
}

module Q2 refines Q1 {
  class C {
    predicate R() { x % 3 == 2 }  // finally, give it a body
  }
}
