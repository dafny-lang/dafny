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

datatype ADT = FooC(x: int, y: int)

ghost method letTest() {
  assert simp(Foo(var (FooC(a, b), c) := (FooC(7, 8), 9); a)) == 42;
}
