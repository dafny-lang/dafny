// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M1
{
  trait T1
  {
    method M1 (a:int)
  }
  trait T2 
  {
    method M2 (a:int)
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
  import opened M1
  class C2 extends T1  // error: currently no support to implement trait in different module
  {
  }
  class {:termination false} C3 extends T1  // error: currently no support to implement trait in different module
  {
  }

  @asdf
  trait T3 extends T1
  {

  }
  trait T4 extends T3
  {
    
  }
}

module M3
{
  import M1
  
  @AssumeTermination
  class C2 extends M1.T1  // error: currently no support to implement trait in different module
  {
  }
}
