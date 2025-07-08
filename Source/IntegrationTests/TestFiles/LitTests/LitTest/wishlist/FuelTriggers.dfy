// RUN: %testDafnyForEachResolver "%s"

// THIS USED TO BE THE CASE:
//
//     With the default version of opaque + fuel, the following fails to verify
//     because the quantifier in the requires used a trigger that included
//     StartFuel_P, while the assert used StartFuelAssert_P.  Since P is
//     opaque, we can't tell that those fuels are the same, and hence the
//     trigger never fires. A wish would be to fix this.
//
// This has been fixed, so the test assertion is now passing.

opaque ghost predicate P(x:int)

method Test(y:int)
  requires forall x :: P(x)
{
  assert P(y);
}
