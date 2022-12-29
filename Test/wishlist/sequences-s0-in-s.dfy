// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The following is also due to a weakness in the axiomatization: namely, it is
// not easy to learn, using Dafny's axioms, that s[0] in s. One can of course
// prove it, but it doesn't come for free.

method InSeqTriggers(s: seq<int>, i: nat)
  requires forall x :: x in s ==> x > 0;
  requires |s| > 0 {
    if * {
      // Fails
      assert s[0] > 0; // WISH
    } else if * {
      // Works
      assert s[0] in s;
      assert s[0] > 0;
    }
}

method InSeqNoAutoTriggers(s: seq<int>, i: nat)
  requires forall x {:autotriggers false} :: x in s ==> x > 0;
  requires |s| > 0 {
    assert s[0] > 0; // Works (Z3 matches on $Box above)
}
