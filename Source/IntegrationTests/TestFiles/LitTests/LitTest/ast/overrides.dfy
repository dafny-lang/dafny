// RUN: %testDafnyForEachCompiler %s
 
trait T {
  method foo() returns (r: int)  {
    return 3;
  }
}

trait T2 extends T {
  method foo() returns (r: int)  {
    return 5;
  }
}

class C extends T {
  method foo() returns (r: int) {
    return 4;
  }
}

class D extends T {}
class E extends T2 {}
class F extends T2 {
  method foo() returns (r: int) {
    return 6;
  }
}

method Main() {
  var c := new C;
  var rc := c.foo();
  var d := new D;
  var rd := d.foo();
  var e := new E;
  var re := e.foo();
  var f := new F;
  var rf := f.foo(); 
  var t2: T2 := f;
  var rt2 := t2.foo();
  var t: T := t2;
  var rt := t.foo();
  print rc, ", ", rd, ", ", re, ", ", rf, ", ", rt, ", ", rt2;
}