// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Box {
  constructor() {}
  var x: int
}

function method GetBoxFn(b: Box): int
  reads b
{
  b.x
}

method GetBoxCorrectReads(b: Box) returns (i: int)
  reads b
{
  i := b.x;
}

method GetBoxIncorrectReads(b: Box) returns (i: int)
  reads {}
{
  i := b.x; // Error: insufficient reads clause to read field
}

method SetBox(b: Box, i: int) 
  modifies b
{
  b.x := i;
}