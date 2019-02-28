//RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /dprint:"%t.dfy" "%s"
//RUN: %dafny /dafnyVerify:0 /compile:0 /env:0 /printMode:DllEmbed /dprint:"%t1.dfy" "%t.dfy"
//RUN: %dafny /env:0 /compile:3 /printMode:DllEmbed /dprint:"%t2.dfy" "%t1.dfy" > "%t"
//RUN: %diff "%t1.dfy" "%t2.dfy"
//RUN: %diff "%s.expect" "%t"

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
  class C {
    ghost var h: int  // change from non-ghost to ghost
    ghost var j: int
    var k: int
    method m() 
      ensures h == h
      ensures j == j
    {
      assert k == k;
    }
  }
}
 
method Main() {
  var c := new T.C;
  c.m();
}
