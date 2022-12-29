// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method tautology1(x: int): (y: bool)
  ensures x == 2 ==> y
{
  x >= 2
}
