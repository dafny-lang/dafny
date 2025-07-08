// RUN: %exits-with 2 %run "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function ghostPredicate(x: int): bool {
  x % 2 == 0
}

datatype Cell = Cell(x: int)
type EvenCell = c: Cell | ghostPredicate(c.x) witness Cell(0)

function doubleEvenCell(c: EvenCell): int
{
  if c.x % 2 == 1 then 1/0 else c.x * 2
}

method Main() {
  var x: set<Cell> := { Cell(1), Cell(2), Cell(3), Cell(4) };

  var y: set<EvenCell>;
  var z: map<EvenCell, nat>;
  y := set c: EvenCell | c in x; // error: type test for EvenCell is ghost
  z := map c: EvenCell | c in x :: c.x; // error: type test for EvenCell is ghost

  var b: bool;
  b := forall c: EvenCell :: c in y ==> doubleEvenCell(c) > 0;
  b := forall c: EvenCell :: c in x ==> doubleEvenCell(c) > 0; // error: type test for EvenCell is ghost
}
