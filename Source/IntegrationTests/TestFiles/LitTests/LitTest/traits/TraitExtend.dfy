// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait t
{
  var f: int

  function Plus (x:int, y:int) : int
    requires x>y
  {
    x + y
  }

  function Mul (x:int, y:int, z:int) : int
    requires x>y
  {
    x * y * z
  }

  //function BodyLess1() : int

  static method GetPhoneNumber (code:int, n:int) returns (z:int)
  {
    z := code + n;
  }

  method TestPhone ()
  {
    var num : int;
    num := GetPhoneNumber (10, 30028);
  }
}

class c1 extends t
{
  method P2(x:int, y:int) returns (z:int)
    requires x>y
  {
    z:= Plus(x,y) + Mul (x,y,1);
    var j:int := Mul (x,y);   //error, too few parameters in calling inherited method
    var k:int := Plus(x,y,1); //error, too many parameters in calling inherited method
  }
}
