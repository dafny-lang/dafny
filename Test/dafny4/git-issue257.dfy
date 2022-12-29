// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module  M {
  trait T {
    function f(): nat
  }
  class C extends T {
    constructor () { }
    function f(): nat { 0 }
  }
}

method Test0() {
  var c := new M.C();
  assert c.f() == 0;
  var g: M.T := c;
  assert g.f() == 0;  // used to fail, but shouldn't
}

method Test1() {
  var c := new M.C();  // type is inferred to M.T? :(
  var g: M.T := c;
  assert c.f() == 0;  // which used to cause this to fail, but shouldn't
}

method Test2() {
  var c := new M.C();
  assert c.f() == 0;
}

method Test3() {
  var c: M.C := new M.C();  // explicitly ask for type M.C
  var g: M.T := c;
  assert c.f() == 0;
}

method Test4(c: M.C, g: M.T)
  requires c == g
{
  assert c.f() == 0;
  assert g.f() == 0;  // used to fail, but shouldn't
}
