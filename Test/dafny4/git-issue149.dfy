// RUN: %exits-with 2 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function Foo<T>(m: map<int, T>): seq<T>
    ensures Foo(m) != []

lemma Bar()
    ensures forall m | 0 in m :: Foo(m)[0] == m[0]  // error (x3) -- but should not crash Dafny
{}
