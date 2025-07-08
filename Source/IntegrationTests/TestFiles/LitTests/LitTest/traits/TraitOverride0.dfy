// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


trait T1
{
  var f: int

  function Plus(x:int, y:int) : int
    requires x>y
  {
    x + y
  }

  function Mul(x:int, y:int, z:int) : int
    requires x>y
  {
    x * y * z
  }

  function BodyLess1() : int

  function BodyLess2(a:int, b:int) : int

  static method GetPhoneNumber(code:int, n:int) returns (z:int)
  {
    z := code + n;
  }

  method TestPhone()
  {
    var num : int;
    num := GetPhoneNumber(10, 30028);
  }
}

trait T2
{
}

class C1 extends T1
{
  method P2(x:int, y:int) returns (z:int)
    requires x>y
  {
    z := Plus(x,y) + Mul(x,y,1);
  }

  function BodyLess1(i:int) : int //error, overriding function has too many parameters
  {
    12
  }

  function Mul(x:int, y:int, z:int) : int //error, can not override implemented methods
    requires x>y
  {
    x * y * z
  }

  function BodyLess2(a:int, b:int) : int
  {
    a+b
  }
}

class C2 extends T1
{
  //error, there are body-less methods in the parent trait that must be implemented
}

abstract module AM1
{
  trait T2
  {
    method Calc(i:int, j:int) returns (k:int)
  }

  class T2Client extends T2
  {
    method Calc(ii:int, jj:int) returns (kk:int)
  }
}
