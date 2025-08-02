// RUN: %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Store the old(value) and since we don't yet have twostate invariants
// The stuttering bit has the effect of taking the reflexive closure of the predicate
//   value == old_value + 1
// as if it were a relation on heaps, so that the invariant holds at the end of the constructor
class Counter {
  ghost var old_value: nat
  var value: nat
  var stuttering: bool
  invariant stuttering || value == old_value + 1
  constructor() {
    stuttering := true;
    old_value := 0;
    value     := 0;
  }
  method Increment()
    modifies this
  {
    stuttering := false;
    old_value := value;
    value     := value + 1;
  }
}

lemma ReasonAboutCounter(c: Counter)
  requires !c.stuttering
  ensures c.value == c.old_value + 1
{
  assert c.invariant(); // fire the axiom!
}