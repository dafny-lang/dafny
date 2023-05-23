// RUN: %dafny /compile:3 /errorLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Double constraints. Will this still work?

datatype Cell = Cell(x: int)

// Compilable constraint
type CompilableNaturalCell = cn: Cell | cn.x >= 0 witness Cell(0)

// Compilable constraint
type CompilableOrdinalCell = coc: CompilableNaturalCell | coc.x != 0 witness Cell(1)

predicate compiledOrdinalCellIsOneOrMore(c: CompilableOrdinalCell)
{
  (if c.x <= 0 then 1/0 else c.x) > 1
}

function returnsOneIfCompilableOrdinalCell(c: CompilableOrdinalCell): int
{
  if c.x <= 0 then 1/0 else 1
}

function {:opaque} getOriginalSet(): set<Cell> {
  { Cell(-1), Cell(0), Cell(1), Cell(2) }
}

predicate isSetOfCompilableOrdinalCells(s: set<CompilableOrdinalCell>) {
  forall c :: c in s ==> returnsOneIfCompilableOrdinalCell(c) == 1
}

method Main() {
  var x: set<Cell> := getOriginalSet();
  var b := true;
  b := b && isSetOfCompilableOrdinalCells(set co: CompilableOrdinalCell | co in x && compiledOrdinalCellIsOneOrMore(co) :: co);
  assert b;
  print if b then "ok" else "error";
}
