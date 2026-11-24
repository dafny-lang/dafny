// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The assumption that follows a forall statement assigning to the heap used to assert
// the call facts of its range for every datatype value, not only for values of the
// bound variable's type. Here that contradicted the constructor of r and proved false.

datatype T = T(n: nat)
datatype R = X | Y(k: nat)

method M(a: array<int>, s: set<T>, r: R)
  requires a.Length == 10
  modifies a
  ensures false // error: (but this was once provable, due to a bug)
{
  forall t: T | t.n < 10 && t in s {
    a[t.n] := 0;
  }
  var rs := {r};
}
