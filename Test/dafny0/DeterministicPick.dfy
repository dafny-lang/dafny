// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Specification {
  function method Pick(s: set<int>): int
    requires s != {}
    ensures Pick(s) in s
}

module Attempt_Arbitrary refines Specification {
  function method Pick...
  {
    var x :| x in s;  // error: cannot prove this is deterministic
    x
  }
}

module Attempt_Smallest refines Specification {
  function method Pick...
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
  function method PickFromSingleton<U>(s: set<U>): U
    requires exists y :: y in s && s == {y}
  {
    var x :| x in s; x
  }
  function method PickFromPair<U(==)>(a: U, b: U): U
    requires a != b
  {
    var x :| x in {a,b} && x != a; x
  }
}
