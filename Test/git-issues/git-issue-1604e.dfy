// RUN: %dafny /compile:3 /errorLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Double constraints. Will this still work?

datatype Cell = Cell(x: int)

predicate isNatural(x: int) {
  x >= 0
}

// Ghost constraint
type GhostNaturalCell = gn: Cell | isNatural(gn.x) witness Cell(0)

// Compilable constraint
type CompilableNaturalCell = cn: Cell | cn.x >= 0 witness Cell(0)


predicate isNonZero(x: int) {
  x != 0
}

// Ghost constraint
type GhostOrdinalCell = goc: GhostNaturalCell | isNonZero(goc.x) witness Cell(1)
// Ghost constraint
type GhostOrdinalCell2 = goc2: CompilableNaturalCell | isNonZero(goc2.x) witness Cell(1)
// Ghost constraint
type GhostOrdinalCell3 = goc3: GhostNaturalCell | goc3.x != 0 witness Cell(1)
// Compilable constraint
type CompilableOrdinalCell = coc: CompilableNaturalCell | coc.x != 0 witness Cell(1)

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
  var b := true;

  b := b && isSetOfGhostOrdinalCells(set go: GhostOrdinalCell | go in x && ghostOrdinalCellIsOneOrMore(go) :: go);
  
  b := b && isSetOfGhostOrdinalCells(set go2: GhostOrdinalCell2 | go2 in x && ghostOrdinalCellIsOneOrMore(go2) :: go2);
  
  b := b && isSetOfGhostOrdinalCells(set go3: GhostOrdinalCell3 | go3 in x && ghostOrdinalCellIsOneOrMore(go3) :: go3);

  assert b;
  print if b then "ok" else "error";
}
