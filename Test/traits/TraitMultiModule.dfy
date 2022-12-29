// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
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
  import opened M1
  class C2 extends T1  // error: currently no support to implement trait in different module
  {
  }
}

module M3
{
  import M1
  class C2 extends M1.T1  // error: currently no support to implement trait in different module
  {
  }
}
