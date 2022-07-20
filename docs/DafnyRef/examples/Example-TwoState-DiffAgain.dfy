twostate function DiffAgain(c: Cell, new d: Cell): int
  reads d
{
  d.data - old(c.data)
}

method P(c: Cell) {
  var d := new Cell(10);
  ghost var x := DiffAgain(c, d);
  ghost var y := DiffAgain(d, c); // error: d is not allocated in old state
}
