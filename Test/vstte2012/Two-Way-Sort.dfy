// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This method is a slight generalization of the
// code provided in the problem statement since it
// is generic in the type of the array elements.
method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
}

// This method is a direct translation of the pseudo
// code given in the problem statement.
// The first postcondition expresses that the resulting
// array is sorted, that is, all occurrences of "false"
// come before all occurrences of "true".
// The second postcondition expresses that the post-state
// array is a permutation of the pre-state array. To express
// this, we use Dafny's built-in multisets. The built-in
// function "multiset" takes an array and yields the
// multiset of the array elements.
// Note that Dafny guesses a suitable ranking function
// for the termination proof of the while loop.
// We use the loop guard from the given pseudo-code.  However,
// the program also verifies with the stronger guard "i < j"
// (without changing any of the other specifications or
// annotations).
method two_way_sort(a: array<bool>)
  modifies a
  ensures forall m,n :: 0 <= m < n < a.Length ==> (!a[m] || a[n])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var i := 0;
  var j := a.Length - 1;
  while (i <= j)
    invariant 0 <= i <= j + 1 <= a.Length
    invariant forall m :: 0 <= m < i ==> !a[m]
    invariant forall n :: j < n < a.Length ==> a[n]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    if (!a[i]) {
      i := i+1;
    } else if (a[j]) {
      j := j-1;
    } else {
      swap(a, i, j);
      i := i+1;
      j := j-1;
    }
  }
}
