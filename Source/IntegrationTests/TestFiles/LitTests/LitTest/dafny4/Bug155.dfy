// RUN: %testDafnyForEachResolver "%s"


ghost function foo(m: multiset<object>): int
  reads m
{
  0
}
