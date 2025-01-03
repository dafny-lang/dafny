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