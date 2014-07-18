// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait J 
{
	function method F(x: int): int
	requires x < 100;
	ensures F(x) < 100;
	
	method M(x: int) returns (y: int)
	requires 0 <= x;
	ensures x < y;
}

class C extends J 
{
	function method F(x: int): int
	requires x < 100;
	ensures F(x) < 100;
	{
	   x
	}
	
	method M(x: int) returns (y: int)
	requires -2000 <= x; // a more permissive precondition than in the interface
	ensures 2*x < y; // a more detailed postcondition than in the interface
	{
	   y := (2 * x) + 1;
	}
}