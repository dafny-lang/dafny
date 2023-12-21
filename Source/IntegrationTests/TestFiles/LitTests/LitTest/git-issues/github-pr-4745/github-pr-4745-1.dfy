// NONUNIFORM: Build directive actually runs the program in the RDE backend
// RUN: %baredafny build --target:dfy %s > %t
// RUN: %diff "%s.expect" %t

module Defs {
  method Not(b: bool) returns (n: bool) {
    if b {
      n := false;
    } else {
      n := true;
    }
  }

  method Fibonacci(n: int) decreases * {
    var a := 0;
    var b := 1;
    while b < n decreases * {
      print "a = ", a, ", b = ", b, " :: ";
      a, b := b, a + b;
    }
  }
}

method Main() decreases * {
  var o := Defs.Not(true);
  print o, " ";
  Defs.Fibonacci(10);
}