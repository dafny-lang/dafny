// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


trait J 
{
	function method F(k:int, y: array<int>): int
	  reads y;
	  decreases k;
	
	function method G(y: int): int 
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
}

class C extends J 
{
	function method F(kk:int, yy: array<int>): int
	{ 
	  200 
	}

	method M(kk:int) returns (ksos:int) //errors here, M must provide its own specifications
	{
		ksos:=10;	
	}	 
}