// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *

// With the default version of opaque + fuel, the following fails to verify
// because the quantifier in the requires used a trigger that included
// StartFuel_P, while the assert used StartFuelAssert_P.  Since P is
// opaque, we can't tell that those fuels are the same, and hence the
// trigger never fires. A wish would be to fix this.

predicate {:opaque} P(x:int)

method test(y:int)
  requires forall x :: P(x)
{
  assert P(y);
}
