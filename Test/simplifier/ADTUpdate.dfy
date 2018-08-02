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

datatype A = A(x: int)

ghost method g()
{
  assert simp(Foo(A(8).(x := 7).x)) == 42;
}
