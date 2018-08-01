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

function method {:simp} const7(): int
{
  7
}

function method {:simp} const7P<T>(x: T): int
{
  7
}

method test<S>(x: S) {
  assert simp(Foo(const7())) == 42;
  assert simp(Foo(const7P(x))) == 42;
}

