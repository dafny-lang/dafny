// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


ghost function f1(d:int):map<int,int>
ghost function f2(y:int, d:int):int

method M(m:map<int,int>, d:int, x2:int)
{
  assert forall d :: f1(d) == (map x | x in m ::  f2(x, d));
}
