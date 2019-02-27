// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var x: int
  // for variety, the following tests the use of an instance Main method
  method Main(ghost u: int) returns (ghost r: bool, ghost s: bool) {
    print "hello, instance\n";
    print "x is ", x, "\n";
  }
}
