// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma Foo(s: seq<int>, i: int)
    requires 0 <= i < |s| - 1
    ensures s[i] == s[i+1]
{}

lemma CallFoo(s: seq<int>)
{
    forall i | 0 <= i < |s| - 1
    {
        Foo(s, i);
    }
}
