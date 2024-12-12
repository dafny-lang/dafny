// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M1
{
  trait T1
  {
    method M1 (a:int)
  }
  trait {:termination false} T2 
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
    method M1 (a:int) {}
  }
  class C3 extends T2  // no error because of {:termination false} on the trait
  {
    method M1 (a:int) {}
  }
  @AssumeCrossModuleTermination
  class C4 extends T1  // no error because of @AssumeCrossModuleTermination on this class
  {
    method M1 (a:int) {}
  }

  trait T3 extends T1  // error: currently no support to implement trait in different module
  {
  }
  trait T4 extends T2  // no error because of @AssumeCrossModuleTermination on this trait
  {
  }
}


module M3 
{
  import opened M1

  // This trait is in a separate module without resolution errors
  // so we can extend it in another module and still get resolution errors there.
  @AssumeCrossModuleTermination
  trait T6 extends T1  // no error because of @AssumeCrossModuleTermination on this trait
  {
  }
}

module M4
{
  import M3
  
  class C2 extends M3.T6 // Still an error: @AssumeCrossModuleTermination doesn't imply {:termination false}
  {
    method M1 (a:int) {}
  }
  @AssumeCrossModuleTermination
  class C3 extends M3.T6  // no error because of @AssumeCrossModuleTermination on this trait
  {
    method M1 (a:int) {}
  }
}
