// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

iterator MyIter<T(0)>(q: T) yields (x: T, y: T)
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
  var m := new MyIter(12);
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

  var n := new MyIntIter();
  var patience := 10;
  while (patience != 0)
    invariant n.Valid() && fresh(n._new);
  {
    var more := n.MoveNext();
    if (!more) { break; }
    print n.x, ", ", n.y, "\n";
    patience := patience - 1;
  }

  var o := new Naturals(18);
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

iterator IterA(c: Cell?)
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
  var iter := new IterA(c);
  var tmp := c.data;
  var more := iter.MoveNext();
  assert tmp == c.data;  // error
}

// -----------------------------------------------------------

iterator IterB(c: Cell?)
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
  var iter := new IterB(c);
  var tmp := c.data;
  var more := iter.MoveNext();
  if (more) {
    assert tmp == c.data;  // no prob
  } else {
    assert tmp == c.data;  // error: the postcondition says nothing about this
  }
}

// ------------------ yield statements, and_decreases variables ----------------------------------

iterator IterC(c: Cell?)
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
  var iter := new IterC(c);
  var tmp := c.data;
  var more := iter.MoveNext();
  if (more) {
    assert tmp == c.data;  // no prob
  } else {
    assert tmp == c.data;  // error: the postcondition says nothing about this
  }

  iter := new IterC(c);
  c.data := 17;
  more := iter.MoveNext();  // error: iter.Valid() may not hold
}

// ------------------ allocations inside an iterator ------------------

iterator AllocationIterator(x: Cell?)
{
  assert _new == {};
  var h := new Cell;
  assert _new == {h};

  SomeMethod();
  assert x !in _new;
  assert null !in _new;
  assert h in _new;

  ghost var saveNew := _new;
  var u, v := AnotherMethod();
  assert u in _new;
  if {
    case true =>  assert v in _new - saveNew ==> v != null && fresh(v);
    case true =>  assert !fresh(v) ==> v !in _new;
    case true =>  assert v in _new;  // error: it may be, but, then again, it may not be
  }
}

method SomeMethod()
{
}

method AnotherMethod() returns (u: Cell?, v: Cell?)
  ensures u != null && fresh(u);
{
  u := new Cell;
}

iterator DoleOutReferences(u: Cell?) yields (r: Cell?, c: Cell?)
  yield ensures r != null && fresh(r) && r !in _new;
  yield ensures c != null && fresh(c);  // but we don't say whether it's in _new
  ensures false;  // goes forever
{
  var myCells: seq<Cell?> := [];
  while (true)
    invariant forall z :: z in myCells ==> z in _new;
  {
    c := new Cell;
    r := new Cell;
    c.data, r.data := 12, 12;
    myCells := myCells + [c];
    _new := _new - {r};  // remove our interest in 'r'
    yield;
    if (*) {
      _new := _new + {c};  // fine, since 'c' is already in _new
      _new := _new + {u};  // error: this does not shrink the set
    } else if (*) {
      assert c.data == 12;  // still true, since 'c' is in _new
      assert c in _new;  // as is checked here as well
      assert r.data == 12;  // error: it may have changed
    } else {
      forall z | z in myCells {
        z.data := z.data + 1;  // we're allowed to modify these, because they are all in _new
      }
    }
  }
}

method ClientOfNewReferences()
{
  var m := new DoleOutReferences(null);
  var i := 86;
  while (i != 0)
    invariant m.Valid() && fresh(m._new);
  {
    var more := m.MoveNext();
    assert more;  // follows from 'ensures' clause of the iterator
    if (*) {
      m.r.data := i;  // this change is allowed, because we own it
    } else {
      m.c.data := i;  // this change, by itself, is allowed
      assert m.Valid();  // error:  ... however, don't expect m.Valid() to survive the change to m.c.data
    }
    i := i - 1;
  }
}

// ------ recursive iterators --------------------------------------

module ITER_A {
  iterator RecursiveIterator(n: nat, r: RecIterCaller?, good: bool)
    requires r != null;
    decreases n+2, 0;
  {
    if n == 0 {
    } else if good {
      r.M(n - 1);
    } else {
      r.M(n + 1);  // error: may fail to terminate
    }
  }

  class RecIterCaller {
    method M(n: nat)
      decreases n+2;
    {
      var good;
      var iter := new RecursiveIterator(n, this, good);
      var more := iter.MoveNext();
    }
  }
}
module ITER_B {
  iterator RecursiveIterator(n: nat, r: RecIterCaller?, good: bool)
    requires r != null;
    decreases n;
  {
    if n == 0 {
    } else if good {
      r.M(n - 1);
    } else {
      r.M(n + 1);  // error: may fail to terminate
    }
  }

  class RecIterCaller {
    method M(n: nat)
      decreases n;
    {
      var good;
      var iter := new RecursiveIterator(n, this, good);
      var more := iter.MoveNext();  // error: failure to decrease variant function
    }
  }
}
module ITER_C {
  iterator RecursiveIterator(n: nat, r: RecIterCaller?, good: bool)
    requires r != null;
  {
    if n == 0 {
    } else if good {
      r.M(n - 1);
    } else {
      r.M(n + 1);  // error: may fail to terminate
    }
  }

  class RecIterCaller {
    method M(n: nat)
    {
      var good;
      var iter := new RecursiveIterator(n, this, good);
      var more := iter.MoveNext();
    }
  }
}
module ITER_D {
  iterator RecursiveIterator(n: nat, r: RecIterCaller?, good: bool)
    requires r != null;
  {
    if n == 0 {
    } else if good {
      r.M(n - 1, {});
    } else {
      r.M(n + 1, {});  // error: may fail to terminate
    }
  }

  class RecIterCaller {
    method M(n: nat, incomparable: set<int>)
    {
      var good;
      var iter := new RecursiveIterator(n, this, good);
      var more := iter.MoveNext();  // error: failure to decrease variant function
    }
  }
}
module ITER_E {
  class Cell {
    var data: nat;
  }
  iterator RecursiveIterator(cell: Cell?, n: nat, r: RecIterCaller?, good: bool)
    requires cell != null && r != null;
    modifies cell;
    decreases if cell.data < 2 then n else n+n-n;
  {
    if n == 0 {
    } else if good {
      r.M(n - 1);
    } else {
      r.M(n + 1);  // error: may fail to terminate
    }
  }

  class RecIterCaller {
    method M(n: nat)
    {
      var good;
      var cell := new Cell;
      var iter := new RecursiveIterator(cell, n, this, good);
      var more := iter.MoveNext();  // error: failure to decrease variant function
    }
  }
}
module ITER_F {
  class Cell {
    var data: nat;
  }
  iterator RecursiveIterator(cell: Cell?, n: nat, r: RecIterCaller?, good: bool)
    requires cell != null && r != null;
    modifies cell;
    decreases if cell.data < 2 then n else n+n-n, 0;
  {
    if n == 0 {
    } else if good {
      r.M(n - 1);
    } else {
      r.M(n + 1);  // error: may fail to terminate
    }
  }

  class RecIterCaller {
    method M(n: nat)
    {
      var good;
      var cell := new Cell;
      var iter := new RecursiveIterator(cell, n, this, good);
      var more := iter.MoveNext();
    }
  }
}

module ModuleWithIterator {
  export
    reveals Iter
  iterator Iter(x: int) yields (y: int) {
  }
}

module IteratorClient_Reveals {
  import ModuleWithIterator
  method M() {
    var iter := new ModuleWithIterator.Iter(5);
  }
}


// ----- loop frames -------------------------------------------------------
// The following contains a regression test, where "this" should be included
// in the loop frame of any loop in an iterator body.

method LoopFrame_OrdinaryMethod(c: Cell) returns (y: int)
  modifies c
  decreases *
{
  y := 10;
  c.data := 10;
  var d := new Cell;
  d.data := 10;
  while true
    invariant y <= 11  // error: may be violated by loop body
    invariant d.data <= 11  // error: may be violated by loop body
    invariant c.data <= 11  // error: may be violated by loop body
    decreases *
  {
    y := y + 1;
    c.data := c.data + 1;
    d.data := d.data + 1;
  }
}

class Cls {
  var y: int
  constructor LoopFrame_Constructor(c: Cell)
    modifies c
    decreases *
  {
    y := 10;
    new;
    c.data := 10;
    var d := new Cell;
    d.data := 10;
    while true
      invariant y <= 11  // error: may be violated by loop body
      invariant d.data <= 11  // error: may be violated by loop body
      invariant c.data <= 11  // error: may be violated by loop body
      decreases *
    {
      y := y + 1;
      c.data := c.data + 1;
      d.data := d.data + 1;
    }
  }
}

iterator LoopFrame_Iter(c: Cell) yields (y: int)
  reads c
  modifies c
  yield ensures |ys| <= 2
{
  yield;
  y := 10;
  c.data := 10;
  var d := new Cell;
  d.data := 10;
  while true
    invariant y <= 11  // error: may be violated by loop body
    invariant d.data <= 11  // error: may be violated by loop body
    invariant c.data <= 11  // error: may be violated by loop body
  {
    if * {
      this.y := this.y + 1;
    } else {
      y := y + 1;
    }
    c.data := c.data + 1;
    d.data := d.data + 1;
    yield;  // error: this may violate the "yield ensures"
  }
}

iterator NewRemainsFresh(x: nat) yields (y: nat)
{
  while *
  {
    assert 0 <= x + y;
    if * {
      assert forall z :: z in _new ==> fresh(z);
    }
    var c := new Cell;
    yield;
    assert forall z :: z in _new ==> fresh(z);
  }
  assert forall z :: z in _new ==> fresh(z);
}
