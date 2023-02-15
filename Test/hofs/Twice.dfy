// RUN: %exits-with 4 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method Twice<A>(f : A ~> A): A ~> A
{
  x requires f.requires(x) && f.requires(f(x))
    reads f.reads(x), if f.requires(x) then f.reads(f(x)) else {}
  => f(f(x))
}

method Simple() {
  assert Twice(x => x + 1)(0) == 2;
  assert Twice(Twice(x => x + 1))(0) == 4;

  assert Twice(Twice)(x => x + 1)(0) == 4;
  assert Twice(Twice)(Twice)(x => x + 1)(0) == 16;
}

method WithReads() {
  var a : array<int> := new int[1];
  a[0] := 1;
  var f := x reads a => x + a[0];
  assert Twice(f)(0) == 2;
  a[0] := 2;
  assert Twice(f)(0) == 4;
  assert Twice(f)(0) == 2; // should fail
  assert false;            // should fail
}


function method Twice_bad<A>(f : A ~> A): A ~> A
{
  x requires f.requires(x) && f.requires(f(x))
    reads f.reads(x) + f.reads(f(x))
  => f(f(x))
}

