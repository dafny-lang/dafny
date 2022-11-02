// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Simple sanity test of nested modules
module Parent {
  module Child {
    method Test() {
      print "hi from a nested module\n";
    }
  }
}

method Main() {
  Parent.Child.Test();
}