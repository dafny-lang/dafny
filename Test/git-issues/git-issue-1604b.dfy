// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Cell = Cell(x: int)

predicate isEven(x: int) {
  x % 2 == 0
}
// Ghost constraint
type GhostEvenCell = c: Cell | isEven(c.x) witness Cell(0)

// Compilable constraint
type CompilableEvenCell = c: Cell | c.x % 2 == 0 witness Cell(0)

predicate method ghostEvenCellIsOneOrMore(c: GhostEvenCell)
{
  (if c.x % 2 == 1 then 1/0 else c.x) > 1
}
predicate method compiledEvenCellIsOneOrMore(c: CompilableEvenCell)
{
  (if c.x % 2 == 1 then 1/0 else c.x) > 1
}

function method returnsOneIfCompilableEvenCell(c: CompilableEvenCell): int
{
  if c.x % 2 == 1 then 1/0 else 1
}
function method returnsOneIfGhostEvenCell(c: GhostEvenCell): int
{
  if c.x % 2 == 1 then 1/0 else 1
}


function method {:opaque} getOriginalSet(): set<Cell> {
  { Cell(1), Cell(2), Cell(3), Cell(4) }
}

predicate method isSetOfGhostEvenCells(s: set<GhostEvenCell>) {
  forall c :: c in s ==> returnsOneIfGhostEvenCell(c) == 1
}
predicate method isSetOfCompilableEvenCells(s: set<GhostEvenCell>) {
  forall c :: c in s ==> returnsOneIfCompilableEvenCell(c) == 1
}
function method isGhostEvenCell(c: Cell): (r: bool)
{
  c.x == 0
}

method Main() {
  var x: set<Cell> := getOriginalSet();

  // TODO: It should fail to prove that the term has type GhostEvenCell
  var b := true;

  // This line should work because c should be of type Cell as the constraint is not compilable
  // Since it figures out the type of c later, it will be resolved as a "GhostEvenCell" everywhere.
  b := b && isSetOfGhostEvenCells(set c | c in x && isGhostEvenCell(c) && ghostEvenCellIsOneOrMore(c) :: c);

  // This line should fail because c should be of type Cell as the constraint is not compilable
  // Since it figures out the type of c later, it will be resolved as a "GhostEvenCell" everywhere.
  b := b && isSetOfGhostEvenCells(set c | c in x && ghostEvenCellIsOneOrMore(c) :: c);
  assert b;
  print if b then "ok" else "error";
}