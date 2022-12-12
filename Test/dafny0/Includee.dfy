// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m_unproven(x:int) returns (y:int)
  ensures y == 2*x;
{  // error: postcondition violation
}

function f(x:int) : int
{
  2*x
}

abstract module Abstract
{
  function method inc(x:int) :int
    ensures inc(x) > x;

  method M(x: int) returns (r: int)
    ensures r == x;
  {  // error: postcondition violation
    var y :| 0 <= y;
    r := x + 3;
    assert r % 3 == 0;  // error
  }

  function method G(x: int): int
}
