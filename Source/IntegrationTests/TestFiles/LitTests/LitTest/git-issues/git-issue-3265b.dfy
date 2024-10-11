// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(x: int): set<int>

method Test(x: int)
  requires forall x: int, y: int, z: int :: x in F(y) * F(z)
{
}