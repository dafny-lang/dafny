// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t" || true
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t" || true
// RUN: %diff "%s.expect" "%t"

method Main() {
  var a := (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21);
  print a, "\n";
}