// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:simp} simp<T>(t: T): T { t }

function {:opaque} Foo(x: int): int
{
  42
}

lemma {:simp} Foo_42(x: int)
  ensures Foo(x) == 42
{
  reveal Foo();
}

method SimpInAssert(x: int) {
  assert simp(Foo(x)) == 42;
}
