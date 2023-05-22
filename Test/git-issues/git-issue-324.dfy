// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Sig {
  class Foo {
    const v: int
    constructor () {}
    method hi()
  }
}

module Impl1 refines Sig {
  class Foo {
    const v := 42
    constructor () {}
    method hi() {
      print "Hello!\n";
    }
  }
}

module Program {
  import opened Impl1: Sig

  method Main() {
    var f := new Foo();
    f.hi();
  }
}

