// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

module A {
  module AA {
    method Main() { print "Main1\n"; }
  }
}

module B {
  class C {
    static method Test() { print "Main2\n"; }
  }
}

method {:main} Main() { print "Test3\n"; }
