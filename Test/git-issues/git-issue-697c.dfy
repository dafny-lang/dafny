// RUN: %exits-with 2 %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function ghostPredicate(x: int): bool {
  x % 2 == 0
}

datatype Cell = Cell(x: int)
type EvenCell = c: Cell | ghostPredicate(c.x) witness Cell(0)

function method doubleEvenCell(c: EvenCell): int
{
  if c.x % 2 == 1 then 1/0 else c.x * 2
}

method Main() {
  var x: set<Cell> := { Cell(1), Cell(2), Cell(3), Cell(4) };
  var y := set c: EvenCell | c in x;
  var z: map<EvenCell, nat> := map c: EvenCell | c in x :: c.x;
  var b := forall c :: c in y ==> doubleEvenCell(c) > 0;
  assert b;
  print b;
}

