// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
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

// No need for the subset constraint to be compilable.
method Main() {
  var a: EvenCell := Cell(2);
  if doubleEvenCell(a) > 0 {
    print "ok";
  }
}

