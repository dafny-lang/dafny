// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


//related compiler changes
//everything works OK in the following code
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