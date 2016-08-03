// RUN: %dafny /ironDafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// In one version of opaque + fuel, the following failed to verify
// because the quantifier in the requires used a trigger that included
// StartFuel_P, while the assert used StartFuelAssert_P.  Since P is 
// opaque, we can't tell that those fuels are the same, and hence the
// trigger never fires

predicate {:opaque} P(x:int)

method test(y:int)
    requires forall x :: P(x);
{
    assert P(y);
}
