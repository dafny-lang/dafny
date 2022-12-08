// RUN: %exits-with 4 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


class C { var u : int; }

method M(f : int ~> int)
  requires f.requires(0);
{
  var init := f(0);
  var o := new C;
  assert init == f(0);
}

method M2()
{
  var c := new C;
  c.u := 0;
  var f := () reads c => c.u;
  var init := f();
  c.u := 1;
  if * {
    assert f() == init; // should fail
  } else {
    assert f() == 1;
  }
}

method M3()
{
  var c := new C;
  c.u := 0;
  var f := () reads c => c.u;
  assert f() == 0;
  c.u := 1;
  assert f() == 1;
  assert f() == 0; // should fail
  assert false;    // should fail
}

method Main() {
   var x := 2;
   var getX := () => x;
   assert getX() == 2;
   x := 3;
   assert getX() == 2;  // the value is copied
}

method Refs() {
  var a := new int[1];
  a[0] := 2;
  var get;
  if * {

    get := () reads a => a[0];       // OK
    assert get() == 2;

    a[0] := 3;
    assert get() == 3;               // OK, the ref is copied, but not the entire array

    a := new int[0];
    assert get() == 3;               // OK, still 3
    assert get() == 0 || get() == 2; // fail: is three!

  } else if * {
    get := () => a[0];               // fail: Not enough read
  } else {
    get := () reads {} => a[0];       // fail: Not enough read
  }
}

method Fiddling(k : int ~> int)
{

  var mkGet := (arr : array<int>) =>
               () reads arr requires arr.Length > 0 => arr[0];

  var a := new int[1];
  var b := new int[1];

  var get := mkGet(a);

  a[0] := 0;
  b[0] := 10;

  assert get() == a[0];

  b[0] := 20;

  assert get() == a[0];
}

method HeapSucc0(k : int ~> int)
  requires k.requires(0);
{
  var init := k(0);
  var a := new object;
  assert k(0) == init;
}

method HeapSucc1(k : int ~> int, c : C?)
  requires k.requires(0);
  requires c !in k.reads(0);
  modifies c;
{
  var init := k(0);
  if ( c != null ) {
    c.u := c.u + 1;
    assert k(0) == init;
  }
}

method HeapSucc2(k : int ~> int, c : C?)
  requires k.requires(0);
  modifies c;
{
  var init := k(0);
  if ( c != null ) {
    c.u := c.u + 1;
    if ( c !in k.reads(0) ) {
      assert k(0) == init;
    } else {
      assert k(0) == init; // Fail
    }
  }
}


