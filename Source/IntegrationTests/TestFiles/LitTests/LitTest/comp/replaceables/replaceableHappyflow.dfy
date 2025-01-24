// RUN: %testDafnyForEachCompiler "%s"

replaceable module FooModule {
  method Foo() returns (i: int) 
    ensures i >= 2
}

abstract module SuchAbstract {
  function OrNot(): int {
    1
  }
}

replaceable module BarModule refines SuchAbstract {
  method Bar() returns (i: int) 
    ensures i >= 1
}


replaceable module BazModule replaces BarModule {
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
  
  ConcreteAbstractImports.Prints();
}

abstract module AbstractImportIsOk {
  import Abstract1 : FooModule
  import Abstract2 : Nesting.ConcreteFoo
  import Abstract3 : FooModule
}

module ConcreteAbstractImports refines AbstractImportIsOk {
  import Abtract1 = Nesting.ConcreteFoo
  import Abtract2 = FooModule
  import Abtract3 = FooModule
  
  method Prints() {
    var x := Abtract1.Foo();
    print x, "\n";
    var y := Abtract2.Foo();
    print y, "\n";
    var z := Abtract3.Foo();
    print z, "\n";
  }
}