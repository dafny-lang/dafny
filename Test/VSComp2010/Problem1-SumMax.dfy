// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
{
  sum := 0;
  max := 0;
  var i := 0;
  while (i < N)
    invariant i <= N && sum <= i * max;
  {
    if (max < a[i]) {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}

method Main()
{
  var a := new int[10];
  a[0] := 9;
  a[1] := 5;
  a[2] := 0;
  a[3] := 2;
  a[4] := 7;
  a[5] := 3;
  a[6] := 2;
  a[7] := 1;
  a[8] := 10;
  a[9] := 6;
  var s, m := M(10, a);
  print "N = ", a.Length, "  sum = ", s, "  max = ", m, "\n";
}
