// RUN: %testDafnyForEachResolver "%s"


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

