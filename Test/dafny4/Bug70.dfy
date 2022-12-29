// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1
{
  datatype d = D()
}

module M2 { import opened M1 }
module M3 { import opened M1 }

module M4
{
  import opened M1  // this is required to access D() unqualified below
  import opened M2  // this causes no name conflict
  import opened M3  // this causes no name conflict
  method Main()
  {
    var x := D();
  }
}
