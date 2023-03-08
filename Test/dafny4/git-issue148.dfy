// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function Foo(f: () -> (), n: nat): nat
{
    if n == 0 then n
    else Foo(f, n - 1)
}

lemma lemma_Foo()
    ensures forall g: () -> () :: Foo(g, 0) == 0  // regression: this had crashed Dafny
{}
