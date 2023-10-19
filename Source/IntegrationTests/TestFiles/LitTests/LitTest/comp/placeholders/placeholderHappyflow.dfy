// RUN: %testDafnyForEachCompiler "%s"

placeholder module FooModule {
  method Foo() returns (i: int) 
    ensures i >= 2
}

abstract module SuchAbstract {
  function OrNot(): int {
    1
  }
}

placeholder module BarModule refines SuchAbstract {
  method Bar() returns (i: int) 
    ensures i >= 1
}


placeholder module BazModule replaces BarModule {
}

module Nesting {
  module ConcreteFoo replaces FooModule {
    method Foo() returns (i: int) {
      return 2;
    }
  }
  
  module ConcreteBaz replaces BazModule {
    method Bar() returns (i: int) {
      return OrNot();
    }
  }
}

method Main() {
  var x := FooModule.Foo();
  print x, "\n";
  var y := BarModule.Bar();
  print y, "\n";
  var z := BazModule.Bar();
  print z, "\n";
}