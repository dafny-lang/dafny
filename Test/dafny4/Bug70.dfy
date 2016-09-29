// RUN: %dafny /compile:0  /ironDafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1
{
  datatype d = D()
}

module M2 { import opened M1 }
module M3 { import opened M1 }

module M4
{
  import opened M2
  import opened M3
  method Main()
  {
    var x := D();
  }
}
