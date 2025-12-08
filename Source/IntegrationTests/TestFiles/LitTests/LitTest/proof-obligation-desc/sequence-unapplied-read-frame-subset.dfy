// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=datatype --general-newtypes --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ReadUnapplied(c: Cell)
  reads {}
{
  if
  case true =>
    var arr := new int[10](_ reads c => c.data); // error: insufficient reads // BUG: missing check
  case true =>
    var x := c.data; // error: insufficient reads
  case true =>
    var x := ReadAnObject(c); // error: insufficient reads
  case true =>
    var f := ReadAnObject;
    var x := f(c); // error: insufficient reads
  case true =>
    var s := seq(10, _ reads c => c.data); // error: insufficient reads
}

class Cell {
  var data: int
}

function ReadAnObject(c: Cell): int
  reads c
{
  c.data
}