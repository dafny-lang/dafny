// RUN: ! %resolve %s > %t
// RUN: %diff "%s.expect" "%t"

// Currently this creates a resolution error.
replaceable module FooModule {
  method Foo() returns (i: int) 
    ensures i >= 2
}

module Replacement1 replaces FooModule {
  method Bar() returns (i: int) 
    ensures i >= 1
}

module Replacement2 replaces FooModule {
}