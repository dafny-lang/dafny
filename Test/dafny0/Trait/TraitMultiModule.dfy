// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1
{
  trait T1
  {
     method M1 (a:int)    
  }
  class C1 extends T1
  {
     method M1 (x:int)
     {
        var y: int := x;
     }
  }
}

module M2
{
   class C2 extends T1
   {
   
   }

} 