// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
abstract module FooM {

  method Foo(x: int) returns (r: int) modifies match x { case 0 => {} case _ => {} } ensures r == 3
}

abstract module Bla {
  import Operations : FooM

  method Foo(x: int) returns (r: int) {
    r := Operations.Foo(3);
  }
}