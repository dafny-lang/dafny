// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T1
{
   function method Plus (x:int, y:int) : int
     requires x>y;
   {
      x + y
   }
   
   function method bb(x:int):int
     requires x>10;
   
   function method BodyLess1(a:int) : int
     requires a > 0;
    
   function method dd(a:int) : int  
    
   method Testing()  
}

class C1 extends T1
{
   function method dd(x:int):int
   {
     2	
   }
   
   method Testing()
   {
      var x:int := 11;
      x := bb(x);
   }
   
   function method bb(x:int):int
     requires x >10;
   {
     x
   }
   function method BodyLess1(bda:int) : int
    requires bda > (-10); 
   {
     2
   }
   
   method CallBodyLess(x:int)
     requires x > (-10);
   {
	var k:int := BodyLess1(x);
        assert (k==2);
   }
}

