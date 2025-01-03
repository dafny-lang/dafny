// NONUNIFORM: Test still fails on CS (https://github.com/dafny-lang/dafny/issues/5746)
// RUN: %run --target java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


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