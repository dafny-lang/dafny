// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simplifier} simp<T>(t: T): T { t }

function method {:opaque} Foo(x: int): int
{
  x
}

lemma {:simp} Foo_84(x: int)
  ensures Foo(x) + Foo(x) == 2 * x
{
  reveal Foo();
}

method SimpTest(x: int) {
  assert simp(Foo(3) + Foo(3)) == 6;
}
