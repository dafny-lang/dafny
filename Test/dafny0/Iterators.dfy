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

iterator Naturals(u: int) yields (n: nat)
  requires u < 25;  // just to have some precondition
  ensures false;  // never ends
{
  n := 0;
  while (true)
  {
    yield n;
    n := n + 1;
  }
}

method Main() {
  var m := new MyIter.MyIter(12);
  assert m.ys == m.xs == [];
  var a := m.x;
  if (a <= 13) {
    print "-- ", m.x, " --\n";
  }

  var mer := m.MoveNext();
  if (mer) {
    mer := m.MoveNext();
    mer := m.MoveNext();  // error
  }

  var n := new MyIntIter.MyIntIter();
  var patience := 10;
  while (patience != 0)
    invariant n.Valid() && fresh(n._new);
  {
    var more := n.MoveNext();
    if (!more) { break; }
    print n.x, ", ", n.y, "\n";
    patience := patience - 1;
  }

  var o := new Naturals.Naturals(18);
  var remaining := 100;
  while (remaining != 0)
    invariant o.Valid() && fresh(o._new);
  {
    var more := o.MoveNext();
    assert more;
    print o.n, " ";
    remaining := remaining - 1;
    if (remaining % 10 == 0) { print "\n"; }
  }
}

// -----------------------------------------------------------

class Cell {
  var data: int;
}

iterator IterA(c: Cell)
  requires c != null;
  modifies c;
{
  while (true) {
    c.data := *;
    yield;
  }
}

method TestIterA()
{
  var c := new Cell;
  var iter := new IterA.IterA(c);
  var tmp := c.data;
  var more := iter.MoveNext();
  assert tmp == c.data;  // error
}

// -----------------------------------------------------------

iterator IterB(c: Cell)
  requires c != null;
  modifies c;
  yield ensures c.data == old(c.data);
  ensures true;
  decreases c, c != null, c.data;
{
  assert _decreases0 == c;
  assert _decreases1 == (c != null);
  assert _decreases2 == c.data;  // error: c is not protected by the reads clause
  var tmp := c.data;
  if (*) { yield; }
  assert tmp == c.data;  // error: c is not protected by the reads clause
  c.data := *;
}

method TestIterB()
{
  var c := new Cell;
  var iter := new IterB.IterB(c);
  var tmp := c.data;
  var more := iter.MoveNext();
  if (more) {
    assert tmp == c.data;  // no prob
  } else {
    assert tmp == c.data;  // error: the postcondition says nothing about this
  }
}

// -----------------------------------------------------------

iterator IterC(c: Cell)
  requires c != null;
  modifies c;
  reads c;
  yield ensures c.data == old(c.data);
  ensures true;
  decreases c, c, c.data;
{
  assert _decreases2 == c.data;  // this time, all is fine, because the iterator has an appropriate reads clause
  var tmp := c.data;
  if (*) { yield; }
  if (*) { yield; }
  assert tmp == c.data;  // this time, all is fine, because the iterator has an appropriate reads clause
  c.data := *;
}

method TestIterC()
{
  var c := new Cell;
  var iter := new IterC.IterC(c);
  var tmp := c.data;
  var more := iter.MoveNext();
  if (more) {
    assert tmp == c.data;  // no prob
  } else {
    assert tmp == c.data;  // error: the postcondition says nothing about this
  }

  iter := new IterC.IterC(c);
  c.data := 17;
  more := iter.MoveNext();  // error: iter.Valid() may not hold
}

