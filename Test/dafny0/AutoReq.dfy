// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f(x:int) : bool
  requires x > 3;
{
  x > 7
}

// Should cause a function-requires failure
function g(y:int) : bool
{
  f(y)
}

// Should succeed thanks to auto-generation based on f's requirements
function {:autoReq} h(y:int) : bool
{
  f(y)
}

// Should fail based on h's inferred requirements
function h_tester() : bool
{
  h(2)
}

// Should succeed thanks to auto_reqs
function {:autoReq} i(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}

method test()
{
  // Function req violations (and assertion violations)
  if (*) {
    assert i(1, true);
  } else if (*) {
    assert i(0, false);
  }

  // Make sure function i's reqs can be satisfied
  if (*) {
    assert i(3, true);    // False assertion
  }
  assert i(7, false);     // True  assertion
}

module {:autoReq} TwoLayersOfRequires {
  function f(x:int) : bool
    requires x > 4;
  {
    x > 5
  }

  function g(y:int) : bool
    requires y < 50;
  {
    f(y)
  }

  function h(z:int) : bool
  {
    g(z)
  }
}

module {:autoReq} QuantifierTestsSimple {
  function byte(x:int) : bool
  {
    0 <= x < 256
  }

  function f_forall(s:seq<int>) : bool
  {
    forall i :: 0 <= i < |s| ==> byte(s[i])
  }

  function f_exists(s:seq<int>) : bool
  {
    exists i :: 0 <= i < |s| && byte(s[i])
  }

  function g_forall(s:seq<int>) : bool
    requires f_forall(s);
  {
    |s| > 2
  }

  function g_exists(s:seq<int>) : bool
    requires f_exists(s);
  {
    |s| > 2
  }

  function h(s:seq<int>) : bool
  {
    g_forall(s) && g_exists(s)
  }
}

module {:autoReq} QuantifierTestsHard {
  function byte(x:int) : bool
    requires 0 <= x < 256;
  { true }

  function f_forall(s:seq<int>) : bool
  {
    forall i :: 0 <= i < |s| ==> byte(s[i])
  }

  function f_exists(s:seq<int>) : bool
  {
    exists i :: 0 <= i < |s| && byte(s[i])
  }

  function g_forall(s:seq<int>) : bool
    requires forall j :: 0 <= j < |s| ==> byte(s[j]);
  {
    |s| > 2
  }

  function h_forall(s:seq<int>) : bool
  {
    f_forall(s)
  }

  function h(s:seq<int>) : bool
  {
    g_forall(s)
  }

  function i(s:seq<int>) : bool
    requires forall k :: 0 <= k < |s| ==> 0 <= s[k] < 5;
  {
    true
  }

  function j(s:seq<int>) : bool
  {
    i(s)
  }

  function m(x:int) : bool
  function n(x:int) : bool

  function f1(x:int) : bool
  requires x > 3;
  requires x < 16;

  function variable_uniqueness_test(x:int) : bool
  {
    (forall y:int :: m(y))
    &&
    f1(x)
  }
}

module CorrectReqOrdering {
  function f1(x:int) : bool
    requires x > 3;

  function f2(b:bool) : bool
    requires b;

  // Should pass if done correctly.
  // However, if Dafny incorrectly put the requires for f2 first,
  // then the requires for f1 won't be satisfied
  function {:autoReq} f3(z:int) : bool
  {
    f2(f1(z))
  }

}

module ShortCircuiting {
  function f1(x:int) : bool
    requires x > 3;

  function f2(y:int) : bool
    requires y < 10;

  function {:autoReq} test1(x':int, y':int) : bool
  {
    f1(x') && f2(y')
  }

  function {:autoReq} test2(x':int, y':int) : bool
  {
    f1(x') ==> f2(y')
  }

  function {:autoReq} test3(x':int, y':int) : bool
  {
    f1(x') || f2(y')
  }
}

module Lets {
  function f1(x:int) : bool
    requires x > 3;

  function {:autoReq} test1(x':int) : bool
  {
    var y' := 3*x'; f1(y')
  }
}

// Test nested module specification of :autoReq attribute
module {:autoReq} M1 {
  module M2 {
    function f(x:int) : bool
      requires x > 3;
    {
      x > 7
    }

    // Should succeed thanks to auto-generation based on f's requirements
    function {:autoReq} h(y:int) : bool
    {
      f(y)
    }
  }
}

module Datatypes {
  datatype TheType = TheType_builder(x:int) | TheType_copier(t:TheType)

  function f1(t:TheType):bool
    requires t.TheType_builder? && t.x > 3;

  function {:autoReq} test(t:TheType) : bool
  {
    f1(t)
  }

  function f2(x:int) : bool
    requires forall t:TheType :: t.TheType_builder? && t.x > x;
  {
    true
  }

  // Should cause a function-requirement violation without autoReq
  function f3(y:int) : bool
  {
    f2(y)
  }

  function {:autoReq} test2(z:int) : bool
  {
    f2(z)
  }

}

module Matches {
  datatype TheType = TheType_builder(x:int) | TheType_copier(t:TheType)

  function f1(x:int):bool
    requires x > 3;

  function {:autoReq} basic_test(t:TheType) : bool
  {
    match t
      case TheType_builder(x) => f1(x)
      case TheType_copier(t) => true
  }
}

// Make sure :autoReq works with static functions
module StaticTest {
  function f(x:int) : bool
    requires x > 3;
  {
    x > 7
  }

  function {:autoReq} g(z:int) : bool
    requires f(z);
  {
    true
  }

  // Should succeed thanks to auto-generation based on f's requirements
  function {:autoReq} h(y:int) : bool
  {
    g(y)
  }

  predicate IsEven(x:int)

  function EvenDoubler(x:int) : int
    requires IsEven(x);

  // Should succeed thanks to auto-generated requirement of IsEven
  function {:autoReq} test(y:int) : int
  {
    EvenDoubler(y)
  }
}

module OpaqueTest {
  function bar(x:int) : int
    requires x>7;
  {
    x-2
  }

  function {:autoReq} {:opaque} foo(x:int) : int
  {
    bar(x)
  }

}

// autoTriggers added because it causes an extra error message related to
// violated preconditions to appear. That extra message is due to the extra
// precondition involving a split quantifier: the user now gets two traces, one
// for each conjunct.
