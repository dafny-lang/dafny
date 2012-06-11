module A imports B {
  class X {
    function Fx(z: Z): int
      requires z != null;
      decreases 5, 4, 3;
    { z.G() }  // fine; this goes to a different module
  }
  datatype Y = Cons(int, Y) | Empty;
}

class C {
  method M() { }
  function F(): int { 818 }
}

method MyMethod() { }

var MyField: int;

module B {
  class Z {
    method K() { }
    function G(): int
      decreases 10, 8, 6;
    { 25 }
  }
}

static function MyFunction(): int { 5 }

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
    static predicate P(x: int)
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

module B_Visibility imports A_Visibility {
  method Main() {
    var y;
    if (C.P(y)) {
      assert 0 <= y;  // this much is known of C.P
      assert 2 <= y;  // error
    } else {
      assert C.P(8);  // error: C.P cannot be established outside the declaring module
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

module Q_M imports Q_Imp {
  method MyMethod(root: Q_Imp.Node, S: set<Q_Imp.Node>)
    requires root in S;
  {
    var i := new Q_Imp.Node;
    var j := new Node;
    assert i != j;  // fine
    var q := new Q_Imp.Klassy.Init();
  }
}
