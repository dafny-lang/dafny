// RUN: %dafny /compile:0 /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 2, compute the inverse 'B' of a permutation 'A' and prove that 'B' is
// indeed an inverse of 'A' (or at least prove that 'B' is injective).
// Rustan Leino, 31 August 2010.
//
// In the version of this program that I wrote during the week of VSTTE 2010, I had
// used a lemma (stated as a ghost method) that I proved inductively (using a loop and
// a loop invariant).  Here, I have simplified that version by just including an
// assertion of the crucial property, which follows from the surjectivity of 'A'.
//
// The difficulty in proving this program with an SMT solver stems from the fact that
// the quantifier that states the surjectivity property has no good matching trigger
// (because there are no function symbols mentioned in the antecedent of that quantifier,
// only built-in predicates).  Therefore, I introduced a dummy function 'inImage' and
// defined it always to equal 'true'.  I can then mention this function in the crucial
// assertion, which causes the appropriate triggering to take place.
//
// A slight annoyance is that the loop's modifications of the heap, which is checked
// to include only the elements of 'B'.  Since 'A' and 'B' are arrays stored at different
// locations in the heap, it then follows that the elements of 'A' are not modified.
// However, the fact that the heap has changed at all makes the symbolic expressions
// denoting the elements of 'A' look different before and after the heap.  The
// assertion after the loop (which, like all assertions, is proved) is needed to
// connect the two.

method M(N: int, A: array<int>, B: array<int>)
  requires 0 <= N && N == A.Length && N == B.Length && A != B;
  requires forall k :: 0 <= k < N ==> 0 <= A[k] < N;
  requires forall j,k :: 0 <= j < k < N ==> A[j] != A[k];  // A is injective
  requires forall m :: 0 <= m < N && inImage(m) ==> exists k :: 0 <= k && k < N && A[k] == m;  // A is surjective
  modifies B;
  ensures forall k :: 0 <= k < N ==> 0 <= B[k] < N;
  ensures forall k :: 0 <= k < N ==> B[A[k]] == k == A[B[k]];  // A and B are each other's inverses
  ensures forall j,k :: 0 <= j < k < N ==> B[j] != B[k];  // (which means that) B is injective
{
  var n := 0;
  while n < N
    invariant n <= N;
    invariant forall k :: 0 <= k < n ==> B[A[k]] == k;
  {
    B[A[n]] := n;
    n := n + 1;
  }
  assert forall i :: 0 <= i < N ==> A[i] == old(A[i]);  // the elements of A were not changed by the loop
  // it now follows from the surjectivity of A that A is the inverse of B:
  assert forall j :: 0 <= j < N && inImage(j) ==> 0 <= B[j] < N && A[B[j]] == j;
  assert forall j,k :: 0 <= j < k < N ==> B[j] != B[k];
}

ghost function inImage(i: int): bool { true }  // this function is used to trigger the surjective quantification

method Main()
{
  var a := new int[10];
  a[0] := 9;
  a[1] := 3;
  a[2] := 8;
  a[3] := 2;
  a[4] := 7;
  a[5] := 4;
  a[6] := 0;
  a[7] := 1;
  a[8] := 5;
  a[9] := 6;
  var b := new int[10];
  M(10, a, b);
  print "a:\n";
  PrintArray(a);
  print "b:\n";
  PrintArray(b);
}

method PrintArray(a: array<int>)
{
  var i := 0;
  while i < a.Length {
    print a[i], "\n";
    i := i + 1;
  }
}
