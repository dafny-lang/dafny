// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  var b, bb;
  b := new int[] [15, 98, 19];
  bb := Test(b, 0, 2, 10);
  print bb, "\n"; // true
  b := new int[] [17, 98, 19];
  bb := Test(b, 0, 2, 10);
  print bb, "\n"; // false
}

// The nested quantifier in the following code had caused a crash previously, because the `usedSubstMap`
// field in the implementation had been incorrectly cleared.
method Test(b: array<int>, lo: int, hi: int, n: int) returns (bb: bool)
  requires 0 <= lo < hi <= b.Length
{
  bb := forall u :: lo < u < hi ==> RightmostMax(b, b[u-1] + b[u-1], b[u], n) || forall xx :: 0 <= xx < 100 ==> F(xx) == b[u-1];
}

predicate RightmostMax(a: array<int>, r: int, s: int, t: int)
  reads a
{
  2 < a.Length ==> a[2] == r - 11
}

function F(x: int): int {
  3 * x
}
