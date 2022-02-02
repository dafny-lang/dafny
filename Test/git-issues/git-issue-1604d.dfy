// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Double constraints. Will this still work?

datatype Cell = Cell(x: int)

predicate isNatural(x: int) {
  x >= 0
}

// Ghost constraint
type GhostNaturalCell = c: Cell | isNatural(c.x) witness Cell(0)

// Compilable constraint
type CompilableNaturalCell = c: GhostNaturalCell | c.x >= 0 witness Cell(0)


predicate isNonZero(x: int) {
  x != 0
}

// Ghost constraint
type GhostOrdinalCell = c: GhostNaturalCell | isNonZero(c.x) witness Cell(1)
// Ghost constraint
type GhostOrdinalCell2 = c: CompilableNaturalCell | isNonZero(c.x) witness Cell(1)
// Ghost constraint
type GhostOrdinalCell3 = c: GhostNaturalCell | c.x != 0 witness Cell(1)
// Compilable constraint
type CompilableOrdinalCell = c: CompilableNaturalCell | c.x != 0 witness Cell(1)

predicate method ghostOrdinalCellIsOneOrMore(c: GhostOrdinalCell)
{
  (if c.x <= 0 then 1/0 else c.x) > 1
}
predicate method compiledOrdinalCellIsOneOrMore(c: CompilableOrdinalCell)
{
  (if c.x <= 0 then 1/0 else c.x) > 1
}

function method returnsOneIfCompilableOrdinalCell(c: CompilableOrdinalCell): int
{
  if c.x <= 0 then 1/0 else 1
}
function method returnsOneIfGhostOrdinalCell(c: GhostOrdinalCell): int
{
  if c.x <= 0 then 1/0 else 1
}

function method {:opaque} getOriginalSet(): set<Cell> {
  { Cell(-1), Cell(0), Cell(1), Cell(2) }
}

predicate method isSetOfGhostOrdinalCells(s: set<GhostOrdinalCell>) {
  forall c :: c in s ==> returnsOneIfGhostOrdinalCell(c) == 1
}
predicate method isSetOfCompilableOrdinalCells(s: set<CompilableOrdinalCell>) {
  forall c :: c in s ==> returnsOneIfCompilableOrdinalCell(c) == 1
}

method Main() {
  var x: set<Cell> := getOriginalSet();
  // TODO: Test that the following case correctly compile:
  var b := true;

  // This line should work because c should be of type Cell as the constraint is not compilable
  // Since it figures out the type of c later, it will be resolved as a "GhostEvenCell" everywhere.
  b := b && isSetOfGhostOrdinalCells(set c | c in x && c.x >= 1 && ghostOrdinalCellIsOneOrMore(c) :: c);

  b := b && isSetOfCompilableOrdinalCells(set c: CompilableOrdinalCell | c in x && compiledOrdinalCellIsOneOrMore(c) :: c);

  /** The following should fail
  b := b && isSetOfCompilableOrdinalCells(set c: GhostOrdinalCell | c in x && ghostOrdinalCellIsOneOrMore(c) :: c);
  b := b && isSetOfCompilableOrdinalCells(set c: GhostOrdinalCell2 | c in x && ghostOrdinalCellIsOneOrMore(c) :: c);
  b := b && isSetOfCompilableOrdinalCells(set c: GhostOrdinalCell3| c in x && ghostOrdinalCellIsOneOrMore(c) :: c);
  */
}