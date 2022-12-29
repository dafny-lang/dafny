// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function foo(m: multiset<object>): int
  reads m
{
  0
}
