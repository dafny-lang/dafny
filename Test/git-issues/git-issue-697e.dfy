// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Cell = Cell(x: int)
type EvenCell = c: Cell | c.x % 2 == 0 witness Cell(0)

function method doubleEvenCell(f: EvenCell): int
{
  if f.x % 2 == 1 then 1/0 else f.x * 2
}

method Main() {
  var x: set<Cell> := { Cell(1), Cell(2), Cell(3), Cell(4) };
  var b := forall g :: g in x ==> doubleEvenCell(g) > 0;
  assert b;
}

