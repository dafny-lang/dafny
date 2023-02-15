// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The following function gives rise to an inconsistent axiom, except
// for its CanUseFunctionDefs antecedent, which saves the day.
function F(x: int): int
  decreases x;
{
  F(x) + 1  // error: does not decrease termination metric
}

method M()
{
  assert F(5) == 0;  // no error is generated here, because of the inconsistent axiom
  assert false;  // ditto
}
