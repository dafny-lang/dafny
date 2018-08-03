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

lemma {:simp} IfTrue_simp<T>(x: T, y: T)
  ensures (if true then x else y) == x
{}

lemma {:simp} IfFalse_simp<T>(x: T, y: T)
  ensures (if false then x else y) == y
{}

method g(x: bool)
{
  assert simp(Foo(if true && false then 8 else 7)) == 42;
  assert simp(Foo(if true && true then 7 else 8)) == 42;
  assert simp(Foo(if false && x then 8 else 7)) == 42;
  assert simp(Foo(if x && false then 8 else 7)) == 42;

  assert simp(Foo(if (true || false) then 7 else 8)) == 42;
  assert simp(Foo(if false || false then 8 else 7)) == 42;
  assert simp(Foo(if true || x then 7 else 8)) == 42;
  assert simp(Foo(if x || true then 7 else 8)) == 42;

}
