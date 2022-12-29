// RUN: %baredafny verify %args --disable-nonlinear-arithmetic  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function power(n:nat, e:nat) : int

lemma lemma_power()
    ensures forall n:nat, e:nat :: 0 <= n * e && power(n, e) == 5;
{
    forall n:nat, e:nat
        ensures 0 <= n * e && power(n, e) == 5;
    {
        assume false;
    }
}
