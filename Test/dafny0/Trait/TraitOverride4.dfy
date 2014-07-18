// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


trait J 
{
	function method F(y: int): int
	
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
	function method F(y: int): int 
	{ 
	  200 
	}

	method M(kk:int) returns (ksos:int)
	  requires kk > (-1);
	  ensures ksos > 0;
	{
		ksos:=10;	
	}	 
}