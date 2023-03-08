// RUN: %dafny /compile:4 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function tst(x: nat): nat {
    x + 1
}

method Main() {
  var f := tst;
  print f, "\n";
  print tst, "\n";
}
