// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Here is the example reported in issue #125 to cause a crash in Dafny.
// The crash has been fixed.  However, the semantics is not what is suggested
// in a comment in that bug report.  The semantics suggested there said
// that the opened AMA.T would take precedence over AMA2.T in AbstractModuleC.
// That seems weird, even though it would allow Foo(t:T) to type check in
// AbstractModuleC just like it does in AbstractModuleB.  In the semantics
// now implemented, the two opened imports AMA and AMA2 in AbstractModuleC
// have equal standing.  This means that (the inherited) Foo(t:T) in
// AbstractModuleC refers to T ambiguously.
//
// This file tests resolution errors.  The file Bug125more.dfy tests
// verification on similar (bug resolution-correct) examples.

abstract module AbstractModuleA
{
  type T
}

abstract module AbstractModuleB
{
  import opened AMA : AbstractModuleA

  method Foo(t:T)  // resolution error when inherited in AbstractModuleC: T is ambiguous
}

abstract module AbstractModuleC refines AbstractModuleB
{
  import opened AMA2 : AbstractModuleA
}

// Here is another test example:

module LibA {
  class G {
    static function f(x:int) : bool {
      x >= 10
    }
  }

  function g() : bool {
     true
  }
}

module LibB {
  class G {
    static function f(x:int) : bool {
      x < 10
    }
  }

  function g() : bool {
     false
  }
}

module R {
  import opened LibA
}

module S refines R {
  import opened LibB
  method m() {
    assert g();  // resolution error: ambiguous reference to LibA.g / LibB.g
  }

  method m1() {
   assert G.f(20);  // resolution error: ambiguous reference to LibA.G / LibB.G
  }
}

module V {
  import opened LibA
  function g(): int { 4 }
}

module W refines V {
  function g(): int { 5 }  // refinement error: cannot provide a new body for the inherited g()
}
