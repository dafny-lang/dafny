// RUN: ! %run %s > %t
// RUN: %diff "%s.expect" "%t"

replaceable module {:extern "FooNameOverride"} Foo {
  method {:extern "ZazOverride1"} Zaz() returns (i: int) 
    ensures i >= 2
}

module {:extern "BarNameOverride1"} Bar replaces Foo { 
  method {:extern "BarNameOverride2", "ZazOverride2"} Zaz() returns (i: int) 
    ensures i >= 2
}