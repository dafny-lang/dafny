// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simp} simp<T>(t: T): T { t }

function method {:opaque} Foo(x: int): int
{
  42
}

lemma {:simp} Foo_42(x: int)
  ensures Foo(7) == 42
{
  reveal Foo();
}

lemma {:simp} iffalse_simp<T>(x: T, y: T)
  ensures (if false then x else y) == y
{
}

lemma {:simp} iftrue_simp<T>(x: T, y: T)
  ensures (if true then x else y) == x
{
}

method test() {
  assert simp(Foo(if 1 != 2 then 7 else 8)) == 42;
  assert simp(Foo(if "a" != "b" then 7 else 8)) == 42;
  assert simp(Foo(if true != false then 7 else 8)) == 42;

  assert simp(Foo(if 1 != 1 then 8 else 7)) == 42;
  assert simp(Foo(if "a" != "a" then 8 else 7)) == 42;
  assert simp(Foo(if true != true then 8 else 7)) == 42;
}
