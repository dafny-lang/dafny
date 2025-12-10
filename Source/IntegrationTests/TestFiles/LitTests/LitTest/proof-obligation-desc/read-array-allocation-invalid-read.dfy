// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=datatype --general-newtypes --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ReadUnapplied(c: Cell)
  reads {}
{
  if
  case true =>
    var arr := new int[10](_ reads c => c.data); // error: insufficient reads 
  case true =>
    var init := (i: int) reads c => 300;
    var arr := new int[10](init); // error: insufficient reads 
  case true =>
    var arr := new int[10](c.IndexToElement); // error: insufficient reads 
}

method ReadUnappliedInArrayDimensionSizeExpressions(c: Cell)
  reads {}
{
  if
  case true =>
    var arr := new int[ReadAnObject(c)](_ => 100); // error: insufficient reads 
  case true =>
    var arr := new int[ReadAnObject(c)] [20, 30, 40]; // error: insufficient reads 
  case true =>
    var arr := new int[3] [20, ReadAnObject(c), 40]; // error: insufficient reads 
}
  
class Cell {
  var data: nat

  function IndexToElement(i: int): int {
    300
  }
}

function ReadAnObject(c: Cell): nat
  reads c
{
  c.data + 3 - c.data
}