// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate tautology1(x: int): (y: bool)
  ensures x == 2 ==> y
{
  x >= 2
}