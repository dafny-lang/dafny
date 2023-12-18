// RUN: ! %run %s > %t
// RUN: %diff "%s.expect" "%t"

replaceable module {:extern "FooNameOverride"} Foo {
  method {:extern "ZazOverride1"} Zaz() returns (i: int) 
    ensures i >= 2
}

module {:extern "BarNameOverride1"} TwoErrors replaces Foo { 
  // missing error on BarNameOverride2
  method {:extern "BarNameOverride2", "ZazOverride2"} Zaz() returns (i: int) 
    ensures i >= 2
}

replaceable module {:extern "FaaNameOverride"} Faa {
  method {:extern "ZazOverride1"} Zaz() returns (i: int) 
    ensures i >= 2
}

module {:extern} NoErrors replaces Faa { 
  method {:extern "ZazOverride2"} Zaz() returns (i: int) 
    ensures i >= 2
}