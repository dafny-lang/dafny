// NONUNIFORM: Tests printing much more than compilation
// RUN: %resolve --print "%t.dfy" "%s" > "%t"
// RUN: %resolve --print-mode Serialization --print:"%t1.dfy" "%t.dfy" >> "%t"
// RUN: %run --print-mode Serialization --print:"%t2.dfy" "%t1.dfy" >> "%t"
// RUN: %diff "%t1.dfy" "%t2.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

abstract module S {
  class C {
    var f: int
    ghost var g: int
    var h: int
    method m()
      modifies this
  }
}

module T refines S {
  class C ... {
    ghost var h: int  // change from non-ghost to ghost
    ghost var j: int
    var k: int
    constructor () { }
    method m()
      ensures h == h
      ensures j == j
    {
      assert k == k;
    }
  }
}

method Main() {
  var c := new T.C();
  c.m();
}
