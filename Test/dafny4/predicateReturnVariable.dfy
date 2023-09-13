// RUN: %testDafnyForEachResolver "%s"


predicate tautology1(x: int): (y: bool)
  ensures x == 2 ==> y
{
  x >= 2
}