// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"
// Extra check for the C# compiler with the --compile-suffix option.
// RUN: %baredafny build -t:cs --compile-suffix "%s"
// RUN: %OutputCheck --file-to-check "%S/git-issue-6014.cs" "%s"
// Just to make sure that if we use --compile-suffix, we don't do the escape
// CHECK: .*A_Compile\.A.*
// With the class named B_Compile, it becomes B__Compile so there should be no conflict
// Adding this test in case someone changes the underscore escaping rules to account for this possibility
// CHECK: .*B_Compile\.B__Compile.*


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

  module B {
    datatype B_Compile = Whatever
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
