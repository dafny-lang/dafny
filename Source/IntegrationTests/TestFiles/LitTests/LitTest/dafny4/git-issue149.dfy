// RUN: %exits-with 2 %verify --allow-axioms "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function Foo<T>(m: map<int, T>): seq<T>
    ensures Foo(m) != []

lemma Bar()
    ensures forall m | 0 in m :: Foo(m)[0] == m[0]  // error -- but should not crash Dafny
{}
