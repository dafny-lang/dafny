// RUN: %testDafnyForEachCompiler %s -- --type-system-refresh --general-traits=datatype
 
trait T {
  method foo() returns (r: int)  
    ensures r >= 3
  {
    return 3;
  }
}

trait T2 extends T {
  method foo() returns (r: int)  
    ensures r >= 5  
  {
    return 5;
  }
}

class C extends T {
  method foo() returns (r: int)  
    ensures r >= 4 
  {
    return 4;
  }
}

class D extends T {}
class E extends T2 {}
class F extends T2 {
  method foo() returns (r: int)  
    ensures r >= 6 
  {
    return 6;
  }
}

datatype G extends T = G() {
  method foo() returns (r: int)  
    ensures r >= 4 
  {
    return 7;
  }
}

method Main() {
  var c := new C;
  var rc := c.foo();
  assert rc >= 4;
  var d := new D;
  var rd := d.foo();
  assert rd >= 3;
  var e := new E;
  var re := e.foo();
  assert re >= 5;
  var f: F := new F;
  var rf := f.foo(); 
  assert rf >= 6;
  var t2: T2 := f;
  var rt2 := t2.foo();
  assert rt2 >= 5;
  var t: T := t2;
  var rt := t.foo();
  assert rt >= 3;
  var g := G();
  var gt := g.foo(); 
  print rc, ", ", rd, ", ", re, ", ", rf, ", ", rt, ", ", rt2, ", ", gt;
}