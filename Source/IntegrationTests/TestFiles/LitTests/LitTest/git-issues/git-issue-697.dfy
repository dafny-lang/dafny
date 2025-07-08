// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

datatype Cell = Cell(x: int)
type EvenCell = c: Cell | c.x % 2 == 0 witness Cell(0)

function doubleEvenCell(c: EvenCell): int
{
  if c.x % 2 == 1 then 1/0 else c.x * 2
}

method Main() {
  var x: set<Cell> := { Cell(1), Cell(2), Cell(3), Cell(4) };
  var y := set c: EvenCell | c in x;
  var b := forall c :: c in y ==> doubleEvenCell(c) > 0;
  assert b;
  print b;
}

