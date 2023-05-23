// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T1
{
   var f: int;

   function Plus (x:int, y:int) : int
     requires x>y;
   {
      x + y
   }

   function Mul (x:int, y:int, z:int) : int
     requires x>y;
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

trait T2
{
}

class C1 extends T1
{
    method P2(x:int, y:int) returns (z:int)
      requires x>y;
    {
       z:= Plus(x,y) + Mul (x,y,1);
    }
}



method Good() returns (c: C1, t: T1)
ensures c == t;
{
    t := c;
}

method Bad1() returns (c: C1, t: T2)
ensures c == t;
{
    t := c;  //error, C1 has not implemented T2
}

method Bad2() returns (c: C1, t: T1)
ensures c == t;
{
    c := t;  // OK for type resolution, but must be proved
}
