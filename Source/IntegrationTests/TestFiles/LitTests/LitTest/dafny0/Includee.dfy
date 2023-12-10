// RUN: %exits-with 4 %verify --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m_unproven(x:int) returns (y:int)
  ensures y == 2*x
{  // error: postcondition violation
}

ghost function f(x:int) : int
{
  2*x
}

abstract module Abstract
{
  function inc(x:int) :int
    ensures inc(x) > x

  method M(x: int) returns (r: int)
    ensures r == x
  {  // error: postcondition violation
    var y :| 0 <= y;
    r := x + 3;
    assert r % 3 == 0;  // error
  }

  function G(x: int): int
}
