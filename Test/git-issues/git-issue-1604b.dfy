// RUN: %dafny /compile:3 /errorLimit:0 /rprint:"%t.rprint" "%s" > "%t"
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
function method isEvenCell(c: Cell): (r: bool)
{
  c.x == 0
}

method Main() {
  var x: set<Cell> := getOriginalSet();
  var b := true;
  
  // This line should fail because c inside the range should be of type Cell as the constraint is not compilable
  b := b && isSetOfGhostEvenCells(set c | c in x && ghostEvenCellIsOneOrMore(c) :: c);

  // This line should fail because we cannot extract GhostEvenCells directly
  b := b && isSetOfGhostEvenCells(set c: GhostEvenCell | c in x);

  // This line should fail because we cannot prove that c is a GhostEvenCell
  b := b && isSetOfGhostEvenCells(set c: GhostEvenCell | c in x && c.x % 3 == 0 :: c);

  // This line should fail because although the type constraint can be proven, the precondition for ghostEvenCellIsOneOrMore cannot.
  b := b && isSetOfGhostEvenCells(set c | c in x && ghostEvenCellIsOneOrMore(c) && c.x % 2 == 0);

  // This line should fail twice because c should be of type Cell as the constraint is not compilable
  b := b && isSetOfGhostEvenCells(set c: GhostEvenCell | c in x && ghostEvenCellIsOneOrMore(c));

  // This line should fail because although the type constraint can be proven, the precondition for ghostEvenCellIsOneOrMore cannot.
  b := b && isSetOfGhostEvenCells(set c: GhostEvenCell | c in x && ghostEvenCellIsOneOrMore(c) && c.x % 2 == 0);

  // This line fail because the type of c is inferred to be a Cell
  b := b && isSetOfCompilableEvenCells(set c | c in x && compiledEvenCellIsOneOrMore(c) && c.x % 2 == 0);

  assert b;
  print if b then "ok" else "error";
}

