// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simplifier} simp<T>(t: T): T { t }

function method {:opaque} Foo(x: int): int
{
  42
}

lemma {:simp} Foo_42(x: int)
  ensures Foo(7) == 42
{
  reveal Foo();
}

method test() {
  assert simp(Foo(6 + 1)) == 42;
  assert simp(Foo(8 - 1)) == 42;
  assert simp(Foo(2 * 4 - 1)) == 42;
  assert simp(Foo(21 / 3)) == 42;
}
