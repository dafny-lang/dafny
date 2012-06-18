module A {
  class C {
    var x: int;
    predicate P()
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
    {
      x := -28;
    }
  }
}

module B refines A {
  class C {
    predicate P()
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
    predicate Valid
      reads this, Repr;
    {
      this in Repr && null !in Repr &&
      0 <= N
    }
    constructor Init()
      modifies this;
      ensures Valid && fresh(Repr - {this});
    {
      N, Repr := 0, {this};
    }
    method Inc()
      requires Valid;
      modifies Repr;
      ensures old(N) < N;
      ensures Valid && fresh(Repr - old(Repr));
    {
      N := N + 2;
    }
    method Get() returns (n: int)
      requires Valid;
      ensures n == N;
    {
      n := N;
    }
  }
}

module Tight refines Loose {
  class MyNumber {
    predicate Valid
    {
      N % 2 == 0
    }
    constructor Init()
      ensures N == 0;
    method Inc()
      ensures N == old(N) + 2;
  }
}

module UnawareClient imports Loose {
  method Main0() {
    var n := new MyNumber.Init();
    assert n.N == 0;  // error: this is not known
    n.Inc();
    n.Inc();
    var k := n.Get();
    assert k == 4;  // error: this is not known
  }
}

module AwareClient imports Tight {
  method Main1() {
    var n := new MyNumber.Init();
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
    predicate Constrained
      reads this;
    {
      x < 10
    }
    predicate Valid
      reads this;
    {
      x < 100
    }
    method Init()
      modifies this;
      ensures Valid;
    {
      x := 20;
    }
  }
}

module Tricky_Full refines Tricky_Base {
  class Tree {
    predicate Valid
    {
      Constrained  // this causes an error to be generated for the inherited Init
    }
  }
}

// -------- Quantifiers ----------------------------------------

module Q0 {
  class C {
    var x: int;
    predicate P
      reads this;
    {
      true
    }
    method M()
      modifies this;
      ensures forall c: C :: c != null ==> c.P;
    {
    }
    predicate Q
      reads this;
    {
      x < 100
    }
    method N()
      modifies this;
      ensures forall c :: c == this ==> c.Q;
    {
      x := 102;  // error: fails to establish postcondition (but this error should not be repeated in Q1 below)
    }
    predicate R reads this;  // a body-less predicate
  }
}

module Q1 refines Q0 {
  class C {
    predicate P
    {
      x == 18
    }
    predicate R  // no body yet
  }
}

module Q2 refines Q1 {
  class C {
    predicate R { x % 3 == 2 }  // finally, give it a body
  }
}
