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
predicate method isSetOfCompilableEvenCells(s: set<CompilableEvenCell>) {
  forall c :: c in s ==> returnsOneIfCompilableEvenCell(c) == 1
}

method Main() {
  var x: set<Cell> := getOriginalSet();

  var b := true;

  // This line should work because the output type constraint can be proven
  // c should be assigned the type Cell in the range expression, but GhostEvenCell in the term expression
  b := b && isSetOfGhostEvenCells(set c: GhostEvenCell | c in x && c.x % 2 == 0);

  // This line should work because the precondition of ghostEvenCellIsOneOrMore is met
  b := b && isSetOfGhostEvenCells(set c: GhostEvenCell | c in x && c.x % 2 == 0 && ghostEvenCellIsOneOrMore(c));

  // This line should work because the precondition of ghostEvenCellIsOneOrMore is met
  b := b && isSetOfGhostEvenCells(set c | c in x && c.x % 2 == 0 && ghostEvenCellIsOneOrMore(c));

  // This line works because although c is of type Cell, the constraint is not compilable so it is added.
  b := b && isSetOfCompilableEvenCells(set c: CompilableEvenCell | c in x);

  // This line works as well  but since the constraint is compilable, the test runs twice.
  b := b && isSetOfCompilableEvenCells(set c: CompilableEvenCell | c in x && c.x % 2 == 0);

  // This line works because the test is added right after the assignment of c
  b := b && isSetOfCompilableEvenCells(set c: CompilableEvenCell | c in x && compiledEvenCellIsOneOrMore(c));

  // This line works because the test is added right after the assignment of c, although it is evaluated twice.
  b := b && isSetOfCompilableEvenCells(set c: CompilableEvenCell | c in x && c.x % 2 == 0 && compiledEvenCellIsOneOrMore(c));

  // This line works because the test is added right after the assignment of c, although it is evaluated twice.
  b := b && isSetOfCompilableEvenCells(set c: CompilableEvenCell | c in x && compiledEvenCellIsOneOrMore(c) && c.x % 2 == 0);


  // This line should work although the result is not of type set<GhostEvenCell>
  b := b && isSetOfCompilableEvenCells(set c | c in x && c.x % 2 == 0);

  // This line should work although the result is not of type set<GhostEvenCell>
  b := b && isSetOfGhostEvenCells(set c | c in x && c.x % 2 == 0);

  // This line should work because c should be of type CompiledEvenCell as the constraint is compilable
  b := b && isSetOfCompilableEvenCells(set c | c in x && compiledEvenCellIsOneOrMore(c));

  // This line should work because the precondition of ghostEvenCellIsOneOrMore is met
  b := b && isSetOfGhostEvenCells(set c | c in x && c.x % 2 == 0 && ghostEvenCellIsOneOrMore(c));

    // This line should work because the precondition of compiledEvenCellIsOneOrMore is met although it's executed twice
  b := b && isSetOfCompilableEvenCells(set c | c in x && c.x % 2 == 0 && compiledEvenCellIsOneOrMore(c));

    // This line should work because the tpye of c can be inferred to be CompiledEvenCell
  b := b && isSetOfCompilableEvenCells(set c | c in x && compiledEvenCellIsOneOrMore(c) && c.x % 2 == 0);
 //*/
  assert b;
  print if b then "ok" else "error";
}

