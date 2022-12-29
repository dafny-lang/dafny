// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function{:opaque} f(x:int):int { x }

lemma L()
    ensures forall x:int :: f(x) == x
{
    forall x:int
        ensures f(x) == x
    {
        reveal f();
    }
    assert forall x:int :: f(x) == x;
}

