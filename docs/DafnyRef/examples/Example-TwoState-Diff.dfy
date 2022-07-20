twostate function Diff(c: Cell, d: Cell): int
  reads d
{
  d.data - old(c.data)
}

method M(c: Cell) {
  var d := new Cell(10);
  label L:
  ghost var x := Diff@L(c, d);
  ghost var y := Diff(c, d); // error: d is not allocated in old state
}
