// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Repro0 {
  // Largest power of 2 that divides i
  function lsb(i: nat): nat
    requires i > 0
    ensures 0 < lsb(i) <= i
  {
    if i % 2 == 1 then 1 else 2 * lsb(i / 2)
  }

  opaque ghost function sum(s: seq<int>): int
  {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
  }

  class fenwick {
    var N: nat
    ghost var A: seq<int>
    var F: array<int>

    constructor (A': seq<int>)
          ensures F.Length == |A'| + 1
          ensures F.Length > 0
          ensures F.Length > 0 ==> false
          ensures false
    {
      N := |A'|;
      A := A';
      F := new int[|A'| + 1](i => if 0 < i <= |A'| then A'[i - 1] else 0);
      new;

      for i := 1 to F.Length
        modifies F
        // These invariants are complete garbage and wrong
        invariant forall j :: i < j <= N && j - lsb(j) / 2 >= i ==> F[j] == A[j - 1]
        invariant forall j :: 0 < j <= i <= N ==> lsb(j) > 0 && F[j] == sum(A[j - lsb(j)..j]) // error: does not hold on entry
        invariant forall j :: 0 < j < i && i <= j + lsb(j) <= N ==> lsb(j) <= lsb(j + lsb(j)) && F[j + lsb(j)] == A[j + lsb(j) - 1] + sum(A[j + lsb(j) - lsb(j + lsb(j))..j])
        invariant i > 0 ==> false // error: does not hold on entry
      {
        var j := i + lsb(i);
        if j < F.Length {
          F[j] := F[j] + F[i];
          assert F[j] == A[j - 1];
          assert false;
        }
        assert false;
      }
      assert F.Length > 0 ==> false;
    }
  }

  method Main()
    ensures false
  {
    var FT := new fenwick([0]);
    assert false;
    assert 0 == 1;

    assert FT.N == 69;
    print FT.N; // Actually prints 1
  }
}

module Repro1 {
  function lsb(i: nat): nat
    requires i > 0
    ensures 0 < lsb(i) <= i
  {
    if i % 2 == 1 then 1 else 2 * lsb(i / 2)
  }

  opaque ghost function sum(s: seq<int>): int
  {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
  }

  method MMM(A': seq<int>)
    ensures false
  {
    var A: seq<int> := A';
    var N: nat := |A|;
    var F: array<int>;

    F := new int[|A| + 1](i => if 0 < i <= |A| then A[i - 1] else 0);

    for i := 1 to F.Length
      // These invariants are complete garbage and wrong
      invariant forall j :: i < j <= N && j - lsb(j) / 2 >= i ==> F[j] == A[j - 1]
      invariant forall j :: 0 < j <= i <= N ==> lsb(j) > 0 && F[j] == sum(A[j - lsb(j)..j]) // error: does not hold on entry
      invariant forall j :: 0 < j < i && i <= j + lsb(j) <= N ==>
        lsb(j) <= lsb(j + lsb(j)) &&
        F[j + lsb(j)] == A[j + lsb(j) - 1] + sum(A[j + lsb(j) - lsb(j + lsb(j))..j])
      invariant i > 0 ==> false // error: does not hold on entry
    {
      var j := lsb(i);
    }
  }
}

module Repro2 {
  // Largest power of 2 that divides i
  function lsb(i: nat): nat
    requires i > 0
    ensures 0 < lsb(i) <= i
  {
    if i % 2 == 1 then 1 else 2 * lsb(i / 2)
  }

  opaque function sum(s: seq<int>): int {
    0
  }

  method Test (A1: seq<int>) returns (
      N: nat,
      ghost A: seq<int>,
      F: array<int>
    )
    ensures false
  {
    N := |A1|;
    A := A1;
    F := new int[|A1| + 1](i => if 0 < i <= |A1| then A1[i - 1] else 0);
    for i := 1 to 1
      invariant (forall j :: (i < j <= N && j - lsb(j) >= i ==> F[j] == A[j - 1]))
      invariant (forall j :: (0 < j <= i ==> 0 < lsb(j) == 0)) // error: does not hold on entry
      invariant (forall j :: 0 < j < i ==> 0 < lsb(j) && F[lsb(j)] == sum(A[lsb(j + lsb(j))..]))
      invariant i > 0
    {
      assert false;
    }
    assert false; // error
  }
}

module RegressionTest {
  // The nested quantifier in the following code had caused a crash previously, because the `usedSubstMap`
  // field in the implementation had been incorrectly cleared.
  method Test(b: array<int>, lo: int, hi: int, n: int)
    requires 0 <= lo < hi <= b.Length
    requires lo + 2 == hi
    requires b[lo] == 15 && b[lo + 1] == 98
    requires RightmostMax(b, 16, 98, n)
  {
    assert forall u :: lo < u < hi ==> RightmostMax(b, b[u-1] + 1, b[u], n) || forall xx :: F(xx) == b[u-1];
  }

  ghost predicate RightmostMax(a: array<int>, lo: int, x: int, hi: int)
  function F(x: int): int
}
