// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
Rustan Leino, 5 Oct 2011

COST Verification Competition, Challenge 1: Maximum in an array
http://foveoos2011.cost-ic0701.org/verification-competition

Given: A non-empty integer array a.

Verify that the index returned by the method max() given below points to
an element maximal in the array.

public class Max {
    public static int max(int[] a) {
        int x = 0;
        int y = a.length-1;

        while (x != y) {
            if (a[x] <= a[y]) x++;
                else y--;
        }
        return x;
    }
}
*/

// Remarks:

// The verification of the loop makes use of a local ghost variable 'm'.  To the
// verifier, this variable is like any other, but the Dafny compiler ignores it.
// In other words, ghost variables and ghost assignments (and specifications,
// for that matter) are included in the program just for the purpose of reasoning
// about the program, and they play no role at run time.

// The only thing that needs to be human-trusted about this program is the
// specification of 'max' (and, since verification challenge asked to prove
// something about a particular piece of code, that the body of 'max', minus
// the ghost constructs, is really that code).

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
// verifies and compiles the program (for this program in less than 2 seconds)
// without further human intervention.

method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
{
  x := 0;
  var y := a.Length - 1;
  ghost var m := y;
  while x != y
    invariant 0 <= x <= y < a.Length
    invariant m == x || m == y
    invariant forall i :: 0 <= i < x ==> a[i] <= a[m]
    invariant forall i :: y < i < a.Length ==> a[i] <= a[m]
  {
    if a[x] <= a[y] {
      x := x + 1;  m := y;
    } else {
      y := y - 1;  m := x;
    }
  }
  return x;
}
