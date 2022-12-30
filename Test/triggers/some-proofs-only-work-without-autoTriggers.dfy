// RUN: %exits-with 4 %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The examples below work nicely with /autoTriggers:0, but break when we use
// /autoTriggers.

// The issue is that the axioms for sequences are missing a number of facts,
// which was not a problem before /autoTriggers and /stricterTriggers, but has
// become one. Here are examples of things that Dafny won’t prove with
// /autoTriggers (I would expect it wouldn’t with stricterTriggers either,
// though the second example is trickier than the first):

method M(a: seq<int>) {
  if * {
    // This fails; it needs the following axiom:
    //   axiom (forall<T> s: Seq T ::
    //    { Seq#Take(s, Seq#Length(s)) }
    //    Seq#Take(s, Seq#Length(s)) == s);
    assume forall x :: x in a ==> x > 0;
    assert forall x :: x in a[..|a|] ==> x > 0;
  } else if * {
    // This fails; it needs the following axiom:
    //   axiom (forall<T> s: Seq T, i: int ::
    //    { Seq#Index(s, i) }
    //    0 <= i && i < Seq#Length(s) ==>
    //    Seq#Contains(s, Seq#Index(s, i)));
    assume forall x :: x in a ==> x > 0;
    assert forall i | 0 <= i < |a| ::  a[i] > 0;
  } else if * {
    assume |a| > 3;
    assume forall x | x in a[..3] :: x > 1;
    // This fails, but here it's a lot harder to know what a good axiom would be.
    assert forall x | x in a[..2] :: x > 1;
  }
}


// In the first case, the Boogie version is
//
//   Seq#Contains(Seq#Take(a#0, Seq#Length(a#0)), $Box(x#0_1)) ⟹ x#0_1 > 0
//
// And of course Z3 picks $Box(x#0_1). The third case is similar.
//
// The problem is of course that knowing that x ∈ a[..2] doesn’t magically give
// you a term that matches x ∈ a[..3]. One could imagine introducing an extra
// symbol in the translation to put x and a together for triggering purposes,
// but that would have the same sort of issues as adding symbols for arithmetic
// operators.
