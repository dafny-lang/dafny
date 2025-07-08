// RUN: ! %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

replaceable module FooModule {
  method Foo() returns (i: int) 
    ensures i >= 2
}

module Nesting {
  module ConcreteFoo replaces FooModule {
    method Foo() returns (i: int) {
      return 2;
    }
  }
}

module FooRefiner refines FooModule {
  method Foo() returns (i: int) {
    return 3;
  }
}

module FooRefiner2 refines FooModule {
}

method Main() {
  var x := FooModule.Foo();
  print x, "\n";
  var y := FooRefiner.Foo();
  print y, "\n";
  var z := FooRefiner2.Foo();
  print z, "\n";
}