// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type foo = m: map<int, int> | forall n <- m.Keys :: m[n] < 5

function addToFoo(m: foo): foo
  ensures false
{
  m[1 := 7]
}