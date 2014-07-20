// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


//everything should work OK in the following program
trait J 
{
	function method F(y: int): int
	function method G(y: int): int { 12 }
	method M(y: int)
	method N(y: int) {  
           var a:int := 100;
	   assert a==100;
	}
}
class C extends J 
{
	function method NewFunc (a:int, b:int) : int
	{
	    a + b
	}
	function method F(y: int): int { 20 }
	method M(y: int) { 
	   var a:int := 100;
	   assert a==100;
	}
}

trait t
{
  function f(s2:int):int
  ensures f(s2) > 0;
  //requires s != null && s.Length > 1;
  //reads s, s2;
}

class c extends t
{
  function f(s3:int):int
  ensures f(s3) > 1;
  //requires s0 != null && s0.Length > (0);
  //reads s0;
  { 
     2
  }
}

trait P1
{
  method M(N: int, a: array<int>) returns (sum: int)
  {
    sum := 1;   
  }
}

class C1 extends P1
{

}

trait TT
{
   static function method M(a:int, b:int) : int
     ensures M(a,b) == a + b;
   {
       a + b
   }
}

class CC extends TT 
{
   method Testing(a:int,b:int)
   {
       assert (TT.M(a,b) == a + b);
   }
}
