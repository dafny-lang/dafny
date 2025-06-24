// RUN: %testDafnyForEachCompiler %s
 
trait T {
  method foo() returns (r: int)  {
    return 3;
  }
}

class C extends T {
  method foo() returns (r: int) {
    return 4;
  }
}

class D extends T {}

method Main() {
  var c := new C;
  var r := c.foo();
  var d := new D;
  var r2 := d.foo();
  print r, ", ", r2;
}