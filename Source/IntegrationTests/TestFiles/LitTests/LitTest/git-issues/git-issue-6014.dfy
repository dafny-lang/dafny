// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" 

module State {

  datatype State = Whatever

}

module Foo {

   import opened State

   const bar: State

   method Main() {
     print "Hello!\n";
  }
}

module Enclosing {

  module A {
    datatype A = Whatever
  }

}

module UsingEnclosing {

   import opened Enclosing

   const bar: A.A

   method Main2() {
     print "Hello!\n";
  }
}

module A {

  trait T<X> extends object {
    var a: X
  }

  class A extends T<int> {
    var x : int
    constructor() {x := 0;}
  }

}

module UsingA {

   import opened A

   method Main3() {
     var b := new A();

     print "Hello!\n";
  }
}
