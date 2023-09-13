// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


// The following function gives rise to an inconsistent axiom, except
// for its CanUseFunctionDefs antecedent, which saves the day.
ghost function F(x: int): int
  decreases x
{
  F(x) + 1  // error: does not decrease termination metric
}

method M()
{
  assert F(5) == 0;  // no error is generated here, because of the inconsistent axiom
  assert false;  // ditto
}
