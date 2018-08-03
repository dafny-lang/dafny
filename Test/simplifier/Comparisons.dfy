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
  assert simp(Foo(if 1 < 2 then 7 else 8)) == 42;
  assert simp(Foo(if 3 < 2 then 8 else 7)) == 42;

  assert simp(Foo(if 1 <= 1 then 7 else 8)) == 42;
  assert simp(Foo(if 3 <= 2 then 8 else 7)) == 42;

  assert simp(Foo(if 22 > 1 then 7 else 8)) == 42;
  assert simp(Foo(if 35 > 59 then 8 else 7)) == 42;

  assert simp(Foo(if 73 >= 73 then 7 else 8)) == 42;
  assert simp(Foo(if 35 >= 59 then 8 else 7)) == 42;
}
