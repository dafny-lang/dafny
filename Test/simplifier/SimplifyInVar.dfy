// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method {:simp} simp<T>(t: T): T { t }

function method {:opaque} Foo(x: int): int
{
  42
}

lemma {:simp} Foo_42(x: int)
  ensures Foo(x) == 42
{
  reveal Foo();
}

method SimpInVar(x: int) {
  var x := simp(Foo(x));
  assert x == 42;
}
