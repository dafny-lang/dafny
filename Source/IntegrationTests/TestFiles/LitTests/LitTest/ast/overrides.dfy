// RUN: %run "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

method Main() {
  var c := new C;
  var r := c.foo();
  print r;
}