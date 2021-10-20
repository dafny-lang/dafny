// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:php "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello, JavaScript! Best, Dafny\n";
  var x := 14;
  print "x is ", x, "\n";
  var y := false;
  print "y is ", y, "\n";
}
