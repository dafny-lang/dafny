// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Specification {
  compiled function Pick(s: set<int>): int
    requires s != {}
    ensures Pick(s) in s
}

module Attempt_Arbitrary refines Specification {
  compiled function Pick...
  {
    var x :| x in s;  // error: cannot prove this is deterministic
    x
  }
}

module Attempt_Smallest refines Specification {
  compiled function Pick...
  {
    ASmallestToPick(s);
    var x :| x in s && forall y :: y in s ==> x <= y;
    x
  }
  lemma ASmallestToPick(s: set<int>)
    requires s != {}
    ensures exists x :: x in s && forall y :: y in s ==> x <= y
  {
    var z :| z in s;
    if s != {z} {
      var s' := s - {z};
      assert forall y :: y in s ==> y in s' || y == z;
      ASmallestToPick(s');
    }
  }
}

module AnotherTest {
  compiled function PickFromSingleton<U>(s: set<U>): U
    requires exists y :: y in s && s == {y}
  {
    var x :| x in s; x
  }
  compiled function PickFromPair<U(==)>(a: U, b: U): U
    requires a != b
  {
    var x :| x in {a,b} && x != a; x
  }
}
