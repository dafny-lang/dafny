// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:simplifier} simp<T>(t: T): T { t }

function {:opaque} Foo(x: int): int
{
  42
}

function {:simp} CallSimp(x: int): int
{
  simp(Foo(5))
}

lemma {:simp} Foo_42(x: int)
  ensures Foo(x) == 42
{
  reveal Foo();
}

lemma SimpWorks(x: int)
  ensures CallSimp(x) == 42
{
}
