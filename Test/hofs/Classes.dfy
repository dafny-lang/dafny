// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


class C {
  static function method Static() : bool
  {
    true
  }
}

method K() {
  var f := C.Static;
  var o : object;
  assert o !in f.reads();
  assert f.requires();
  assert f();
}


class T {
  var h : int -> int;
}

function B(t : T) : int -> int
  requires t != null;
  reads t;
{
  t.h
}

function J(t : T) : int
  requires t != null;
  requires t.h.reads(0) == {};
  reads t;
  reads if t != null then t.h.reads(0) else {};
{
  if t.h.requires(0) then
    B(t)(0)
  else
    B(t)(0)  // fail
}

method U(t : T)
  requires t != null;
  modifies t;
{
  t.h := x => x;
  assert J(t) == 0; // ok
}
