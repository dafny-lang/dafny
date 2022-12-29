// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
Rustan Leino, 5 Oct 2011

COST Verification Competition, Challenge 3: Two equal elements
http://foveoos2011.cost-ic0701.org/verification-competition

Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.
*/

// Remarks:

// The implementation of method 'Search' takes one pass through the elements of
// the given array.  To keep track of what it has seen, it allocates an array as
// temporary storage--I imagine that this is what the competition designers
// had in mind, since the problem description says one can assume the values
// of the given array to lie in the range 0..n.

// To keep track of whether it already has found one duplicate, the method
// sets the output variables p and q as follows:
//   p != q   - no duplicates found yet
//   p == q   - one duplicate found so far, namely the value stored in p and q
// Note, the loop invariant does not need to say anything about the state
// of two duplicates having been found, because when the second duplicate is
// found, the method returns.

// What needs to be human-trusted about this program is the specification of
// 'Search'.  The specification straightforwardly lists the assumptions stated
// in the problem description, including the given fact that the array contains
// (at least) two distinct elements that each occurs (at least) twice.  To
// trust the specification of 'Search', a human also needs to trust the definition
// of 'IsDuplicate' and its auxiliary function 'IsPrefixDuplicate'.

// About Dafny:
// As always (when it is successful), Dafny verifies that the program does not
// cause any run-time errors (like array index bounds errors), that the program
// terminates, that expressions and functions are well defined, and that all
// specifications are satisfied.  The language prevents type errors by being type
// safe, prevents dangling pointers by not having an "address-of" or "deallocate"
// operation (which is accommodated at run time by a garbage collector), and
// prevents arithmetic overflow errors by using mathematical integers (which
// is accommodated at run time by using BigNum's).  By proving that programs
// terminate, Dafny proves that a program's time usage is finite, which implies
// that the program's space usage is finite too.  However, executing the
// program may fall short of your hopes if you don't have enough time or
// space; that is, the program may run out of space or may fail to terminate in
// your lifetime, because Dafny does not prove that the time or space needed by
// the program matches your execution environment.  The only input fed to
// the Dafny verifier/compiler is the program text below; Dafny then automatically
// verifies and compiles the program (for this program in less than 11 seconds)
// without further human intervention.

predicate IsDuplicate(a: array<int>, p: int)
  reads a
{
  IsPrefixDuplicate(a, a.Length, p)
}

predicate IsPrefixDuplicate(a: array<int>, k: int, p: int)
  requires 0 <= k <= a.Length;
  reads a;
{
  exists i,j :: 0 <= i < j < k && a[i] == a[j] == p
}

method Search(a: array<int>) returns (p: int, q: int)
  requires 4 <= a.Length;
  requires exists p,q :: p != q && IsDuplicate(a, p) && IsDuplicate(a, q);  // two distinct duplicates exist
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < a.Length - 2;  // the elements of "a" in the range [0.. a.Length-2]
  ensures p != q && IsDuplicate(a, p) && IsDuplicate(a, q);
{
  // allocate an array "d" and initialize its elements to -1.
  var d := new int[a.Length-2];
  var i := 0;
  while (i < d.Length)
    invariant 0 <= i <= d.Length && forall j :: 0 <= j < i ==> d[j] == -1;
  {
    d[i], i := -1, i+1;
  }

  i, p, q := 0, 0, 1;
  while (true)
    invariant 0 <= i < a.Length;
    invariant forall j :: 0 <= j < d.Length ==>
                (d[j] == -1 && forall k :: 0 <= k < i ==> a[k] != j) ||
                (0 <= d[j] < i && a[d[j]] == j);
    invariant p == q ==> IsDuplicate(a, p); //WISH remove the trigger on the next line
    invariant forall k {:trigger old(a[k])} :: 0 <= k < i && IsPrefixDuplicate(a, i, a[k]) ==> p == q == a[k];
    decreases a.Length - i;
  {
    var k := d[a[i]];
    assert k < i;  // note, this assertion is really for human consumption; it is not needed by the verifier, and it does not change the performance of the verifier
    if (k == -1) {
      // a[i] does not exist in a[..i]
      d[a[i]] := i;
    } else {
      // we have encountered a duplicate
      assert a[i] == a[k] && IsDuplicate(a, a[i]);  // note, this assertion is really for human consumption; it is not needed by the verifier, and it does not change the performance of the verifier
      if (p != q) {
        // this is the first duplicate encountered
        p, q := a[i], a[i];
      } else if (p == a[i]) {
        // this is another copy of the same duplicate we have seen before
      } else {
        // this is the second duplicate
        q := a[i];
        return;
      }
    }
    i := i + 1;
  }
}
