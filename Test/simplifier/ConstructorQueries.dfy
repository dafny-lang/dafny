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

lemma {:simp} IfTrue_simp<T>(x: bool, thn: T, els: T)
  ensures (if true then thn else els) == thn
{
}

lemma {:simp} IfFalse_simp<T>(x: bool, thn: T, els: T)
  ensures (if false then thn else els) == els
{
}

datatype ADT = A | B

method test() {
  assert simp(Foo(if A().A? then 7 else 8)) == 42;
  assert simp(Foo(if A().B? then 8 else 7)) == 42;
}

