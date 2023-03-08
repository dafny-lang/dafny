// RUN: %exits-with 4 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type U(==)
ghost function ToU<T>(t:T) : U
type Ptr<T>

class HostEnvironment{
    function{:axiom} heap():map<U,U> reads this;
}

method {:axiom} MakePtr<T>(v:T, ghost env:HostEnvironment) returns (ptr:Ptr<T>) // Using int or seq<T> instead of Ptr<T> eliminates the problem
        modifies env;
        ensures  ToU(ptr) in env.heap();


method test(ghost env:HostEnvironment)
    modifies env;
{
    var myptr := MakePtr(0, env);
    assert ToU(myptr) in env.heap();
}

ghost predicate sat(s:int, t:int)

function{:opaque} and(x:int, y:int):int
    ensures  forall i:int :: sat(i, and(x, y));
{
    2
}
