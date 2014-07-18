// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait I0 
{
   var x: int;
   constructor I0(x0: int) // error: constructor is not allowed in a trait
   {
      x:=x0;
   }
}

trait I1
{
  function M1(x:int,y:int) :int
  {
     x*y
  }
}

method TestI1()
{
   var i1 := new I1; 	//error: new is not allowed in a trait
}

trait I2   		//all is fine in this trait
{
	var x: int;
	
	function method Twice(): int
	 reads this;
	{
		x + x
	}
	
	function method F(z: int): int
	 reads this;

	 
	method Compute(s: bool) returns (t: int, u: int)
	 modifies this;
	{
		if s {
			t, u := F(F(15)), Twice();
		} else {
			t := Twice();
			x := F(45);
			u := Twice();
			var p := Customizable(u);
			return t+p, u;
		}
	}
	
	method Customizable(w: int) returns (p: int)
	 modifies this;

	 
	static method StaticM(a: int) returns (b: int)
	{
		b := a;
	}
	
	static method SS(a: int) returns (b:int)
	{
		b:=a*2;
	}
}

method I2Client(j: I2) returns (p: int)     //all is fine in this client method
 requires j != null;
 modifies j;
{
	j.x := 100;
	var h := j.Twice() + j.F(j.Twice());
	var a, b := j.Compute(h < 33);
	var c, d := j.Compute(33 <= h);
	p := j.Customizable(a + b + c + d);
	p := I2.StaticM(p);
}
