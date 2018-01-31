// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
{
  max := values[0];
  var idx := 0;
  while (idx < |values|)
    invariant max in values
    invariant idx <= |values|
    invariant forall j | 0 <= j < idx :: values[j] <= max
  {
    if (values[idx] > max) {
      max := values[idx];
    }
    idx := idx + 1;
  }
}

lemma MaximumIsUnique(values: seq<int>, m1: int, m2: int)
  requires m1 in values && forall i | 0 <= i < |values| :: values[i] <= m1
  requires m2 in values && forall i | 0 <= i < |values| :: values[i] <= m2
  ensures m1 == m2 {
    // This lemma does not need a body: Dafny is able to prove it correct entirely automatically.
}
