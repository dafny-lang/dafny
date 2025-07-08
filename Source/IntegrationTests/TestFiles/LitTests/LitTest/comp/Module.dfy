// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

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
