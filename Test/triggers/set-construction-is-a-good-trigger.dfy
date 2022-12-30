// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file ensures that display expressions can be picked as triggers. This is
// useful for code that checks if a set, sequence, or multiset is a singleton.

method M(s: seq<int>, st: set<int>, mst: multiset<int>)
  requires exists y :: s == [y]           // Seq#Build(Seq#Empty(): Seq Box, $Box(y#3))
  requires exists y :: st == {y}          // Set#UnionOne(Set#Empty(): Set Box, $Box(y#4))
  requires exists y :: mst == multiset{y} // MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, $Box(y#5))
{
}
