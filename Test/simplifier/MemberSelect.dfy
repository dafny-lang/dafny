// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simplifier} simp<T>(t: T): T { t }

datatype Pair<S, T> = Pair(one: S, two: T)

lemma {:simp} Pair_one_simp<Y, Z>(y: Y, z: Z)
  ensures Pair(y, z).one == y
{
}

function method {:opaque} Foo(x: int): int
{
  42
}

lemma {:simp} Foo_42(x: int)
  ensures Foo(7) == 42
{
  reveal Foo();
}

method f()
{
  assert simp(Foo(Pair(7, 8).one)) == 42;
}
