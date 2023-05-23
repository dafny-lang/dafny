// RUN: %dafny /compile:0 /trace "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L:Verifying AM1.T2Client.Calc (override check) ...
// CHECK-L:Verifying smallPrime (well-formedness) ...
// CHECK-L:Verifying posIdMeth (correctness) ...
newtype smallPrime = x: int | x in {2, 3, 5, 7} witness 2

function posId(x: smallPrime): smallPrime {
  x
}

method posIdMeth(x: smallPrime) returns (r: int)
  ensures r > 0
{
  r := posId(x) as int;
}

abstract module AM1
{
  trait T2
  {
    method Calc(i:int, j:int) returns (k:int)
  }

  class T2Client extends T2
  {
    method Calc(ii:int, jj:int) returns (kk:int)
  }
}
