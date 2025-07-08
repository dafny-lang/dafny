// RUN: %verify --progress Symbol --cores 1 "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L:Verified 0/5 symbols. Waiting for smallPrime to verify.
// CHECK-L:Verified 2/5 symbols. Waiting for posIdMeth to verify.
// CHECK-L:Verified 4/5 symbols. Waiting for AM1.T2Client.Calc to verify.
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
