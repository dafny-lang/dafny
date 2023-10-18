// RUN: %testDafnyForEachCompiler "%s"

placeholder module FooModule {
  method Foo() returns (i: int) 
    ensures i >= 2
}

module Nesting {
  module ConcreteFoo instantiates FooModule {
    method Foo() returns (i: int) {
      return 2;
    }
  }
}

method Main() {
  var x := FooModule.Foo();
  print x, "\n";
}