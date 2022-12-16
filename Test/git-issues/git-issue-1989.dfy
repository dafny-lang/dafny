// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


// ---------------------------------------

predicate P(s: seq<int>)
predicate Q(a: array<int>)
  reads a


method Trigger()
  // The following should generate a warning, but preferably not two.
  // That is, if the old expression is copied into the trigger, it
  // is preferable that there's not a second warning for the 'old' there.
  ensures forall s :: P(s) == old(P(s)) // warning: old has no effect

  // A manually supplied trigger should have its own warning, though:
  ensures forall s {:trigger old(P(s))} :: P(s) == old(P(s)) // warning (x2): old has no effect
{
}
