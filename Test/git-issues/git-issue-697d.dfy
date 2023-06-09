// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function nonGhostPredicate(x: int): bool {
  x % 2 == 0
}

datatype Cell = Cell(x: int)
type EvenCell = c: Cell | nonGhostPredicate(c.x) witness Cell(0)

function doubleEvenCell(c: EvenCell): int
{
  if c.x % 2 == 1 then 1/0 else c.x * 2
}

method Main() {
  var x: set<Cell> := { Cell(1), Cell(2), Cell(3), Cell(4) };
  var y := set c: EvenCell | c in x;
  var b := forall c :: c in y ==> doubleEvenCell(c) > 0;
  var b2 := forall c: EvenCell :: c in x ==> c.x % 2 == 0;
  var b3 := exists c: EvenCell :: c in x && c.x == 3;
  assert b;
  assert b2;
  assert !b3;
  print b && b2 && !b3;
}

