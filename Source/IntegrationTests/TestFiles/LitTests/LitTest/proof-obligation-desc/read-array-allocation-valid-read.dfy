// RUN: %exits-with 0 %verify --type-system-refresh --general-traits=datatype --general-newtypes --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ReadUnapplied(c: Cell)
  reads c
{
  if
  case true =>
    var arr := new int[10](_ reads c => c.data); // error: insufficient reads
}

class Cell {
  var data: int
}

function ReadAnObject(c: Cell): int
  reads c
{
  c.data
}