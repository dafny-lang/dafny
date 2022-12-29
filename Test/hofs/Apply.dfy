// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method Apply(x : int) returns (i : int)
  ensures i == x;
{
  i := (x => x)(x);
}

function method Const<A,B>(a : A) : B -> A {
  b => a
}

method Test(m : map<int, int -> int -> int>)
{
  assume forall i :: i in m;
  assume forall i, x :: m[i].requires(x);
  assume forall i, x, y :: m[i](x).requires(y);
  assume m[1](2)(3) > 5;
  assert ((m[1])(2))(3) > 4;
}

method Main() {
  assert forall x : int, y : int :: Const(x)(y) == (Const(x))(y);
  assert (a => b => a) == (u : int) => (v : int) => u;
}

class Cell {
  var data: int
}

method AllocationTest(oldcell: Cell)
  requires oldcell.data == 48
{
  var y := new Cell;
  y.data := 45;
  var f := () reads y => y.data;
  assert f() == 45;

  var z := new Cell;
  var g := () => if y == z then 30 else 45;
  assert g() == 45;

  if * {
    ghost var d := old(f());  // error: f, which has a reads clause, is not available in old
  } else {
    ghost var e := old(g());  // fine, since g has no reads clause, it is known to produce the same value in any state
    assert e == g();
  }

  var j := (c: Cell, b) => if b then c else oldcell;
  var k := (c: Cell?, b) reads c, oldcell requires b ==> c != null => (if b then c else oldcell).data;
  var b;
  if {
    case true =>  assert j(y, b).data < 50;
    case true =>  assert old(j(y, false).data) == 48;  // error: argument y is not allocated in old state
    case true =>  assert old(j(y, true).data) == 45;  // error: argument y is not allocated in old state
    case true =>  assert old(j(oldcell, b).data) == 48;
    case true =>  assert old(k(oldcell, b)) == 48;
    case true =>  assert old(k(y, b)) < 50;  // error: argument y is not allocated in old state
  }
}
