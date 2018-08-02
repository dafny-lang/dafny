// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simplifier} simp<T>(x: T): T { x }

function method {:opaque} Foo(x: int): int {
  42
}

lemma {:simp} Foo42()
  ensures Foo(7) == 42
{
  reveal Foo();
}

lemma {:simp} Foo42_42()
  ensures Foo(42) == 42
{
  reveal Foo();
}

method g()
{
  var x := simp(Foo(7));
  assert simp(Foo(x)) == 42;
}
