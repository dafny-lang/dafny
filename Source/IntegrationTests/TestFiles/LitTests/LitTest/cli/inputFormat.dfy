// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: ! %verify --input-format Binary %S/Inputs/additional.dfy --stdin < %t.assertFalse.dbin > %t
// RUN: %diff "%s.expect" "%t"

class Fibonacci {
  static function Spec(n: nat): nat
  {
    if n < 2 then
      n
    else
      Spec(n - 1) + Spec(n - 2)
  }

  static method Implementation(n: nat32) returns (r: nat32)
    requires Spec(n) <= 0x7fff_ffff
    ensures r == Spec(n)
  {
    if n == 0 {
      return 1;
    }
    var previousResult: int32 := 0;
    var result: int32 := 1;
    var i: int32 := 1;
    while i < n
      invariant result == Spec(i)
      invariant previousResult == Spec(i - 1)
      invariant i <= n
    {
      i := i + 1;
      SpecIsIncreasing(i, n);
      var addition: int32 := result + previousResult;
      previousResult := result;
      result := addition;
    }
    return result;
  }

  static method SpecIsIncreasing(i: nat, j: nat)
    requires i <= j
    ensures Spec(i) <= Spec(j)
  {
    var x := i;
    while x < j  
      invariant x <= j
      invariant Spec(i) <= Spec(x)
    {
      x := x + 1;
    }
  }
}
