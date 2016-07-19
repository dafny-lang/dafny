// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  import B = Babble
  class X {
    function Fx(z: B.Z): int
      requires z != null;
      decreases 5, 4, 3;
    { z.G() }  // fine; this goes to a different module
  }
  datatype Y = Cons(int, Y) | Empty
}

class C {
  method M() { }
  function F(): int { 818 }
}

method MyMethod() { }



module Babble {
  class Z {
    method K() { }
    function G(): int
      decreases 10, 8, 6;
    { 25 }
  }
}

function MyFunction(): int { 5 }

class D { }

method Proc0(x: int)
  decreases x;
{
  if (0 <= x) {
    Proc1(x - 1);
  }
}

method Proc1(x: int)
  decreases x;
{
  if (0 <= x) {
    Proc0(x - 1);
  }
}

method Botch0(x: int)
  decreases x;
{
  Botch1(x - 1);  // error: failure to keep termination metric bounded
}

method Botch1(x: int)
  decreases x;
{
  Botch0(x);  // error: failure to decrease termination metric
}

// ------ modules ------------------------------------------------

module A_Visibility {
  class C {
    protected static predicate P(x: int)
      ensures P(x) ==> -10 <= x;
    {
      0 <= x
    }
  }
  method Main() {
    var y;
    if (C.P(y)) {
      assert 0 <= y;  // this much is known of C.P
      assert 2 <= y;  // error
    } else {
      assert C.P(8);  // this is fine
    }
  }
}

module B_Visibility {
  import A = A_Visibility
  method Main() {
    var y;
    if (A.C.P(y)) {
      assert -10 <= y;  // this much is known of C.P
      assert 0 <= y;  // error
    } else {
      assert A.C.P(8);  // error: C.P cannot be established outside the declaring module
    }
  }
}

// ------ qualified type names ----------------------------------

module Q_Imp {
  class Node { }
  class Klassy {
    method Init()
  }
}

module Q_M {
  import Q = Q_Imp
  method MyMethod(root: Q.Node, S: set<Q.Node>)
    requires root in S;
  {
    var i := new Q.Node;
    var j := new Q.Node;
    assert i != j;  // fine
    var q := new Q.Klassy.Init();
  }
}

// ----- regression test -----------------------------------------

abstract module Regression {
  module A
  {
    predicate p<c,d>(m: map<c,d>)

    lemma m<a,b>(m: map<a,b>)
      ensures exists m {:nowarn} :: p(var m : map<a,b> := m; m) // WISH: Zeta-expanding the let binding would provide a good trigger
  }

  abstract module B
  {
    import X : A
  }
}
