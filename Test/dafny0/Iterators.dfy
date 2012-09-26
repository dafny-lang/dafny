iterator MyIter<T>(q: T) yields (x: T, y: T)
{
}

iterator MyIntIter() yields (x: int, y: int)
{
  x, y := 0, 0;
  yield;
  yield 2, 3;
  x, y := y, x;
  yield;
}

method Main() {
  var m := new MyIter.MyIter(12);
  var a := m.x;
  // assert !a;  // error: type mismatch
  if (a <= 13) {
    print "-- ", m.x, " --\n";
  }

  var n := new MyIntIter.MyIntIter();
  var patience := 10;
  while (patience != 0) {
    var more := n.MoveNext();
    if (!more) { break; }
    print n.x, ", ", n.y, "\n";
    patience := patience - 1;
  }
}
