// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
trait J
{
  function F(k:int, y: array<int>): int
    reads y;
    decreases k;
    ensures F(k, y) < 100

  function G(y: int): int
  {
    100
  }

  method M(y: int) returns (kobra:int)
    requires y > 0;
    ensures kobra > 0;

  method N(y: int)
  {
    var x: int;
    var y : int;
    y := 10;
    x := 1000;
    y := y + x;
  }

  method arrM (y: array<int>, x: int, a: int, b: int) returns (c: int)
    requires a > b;
    requires y.Length > 0;
    ensures c == a + b;
    modifies y;
    decreases x;
}

class C extends J
{
  // F's postcondition (true) is too weak, but that won't be detected until verification time
  function F(kk:int, yy: array<int>): int
  {
    200
  }

  // M's postcondition (true) is too weak, but that won't be detected until verification time
  method M(kk:int) returns (ksos:int)
  {
    ksos:=10;
  }

  method arrM (y1: array<int>, x1: int, a1: int, b1: int) returns (c1: int)
    requires a1 > b1;
    requires y1.Length > 0;
    ensures c1 == a1 + b1;
    modifies y1;
    decreases x1;
  {
    y1[0] := a1 + b1;
    c1 := a1 + b1;
  }
}
}
module BadNonTermination {
  trait TT1 {
    method N(x: int)
      decreases x
  }
  class CC1 extends TT1 {
    method N(x: int)
      decreases *  // error: can't override a terminating method with a possibly non-terminating method
    { }
  }
}
