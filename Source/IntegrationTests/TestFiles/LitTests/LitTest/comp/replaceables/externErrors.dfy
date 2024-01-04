// RUN: ! %run %s > %t
// RUN: %diff "%s.expect" "%t"

replaceable module {:extern "FooNameOverride"} Foo {
  method {:extern "ZazOverride1"} Zaz() returns (i: int) 
    ensures i >= 2

  method {:extern "ZapOverride1"} Zap() returns (i: int) 
    ensures i >= 2
}

module {:extern "BarNameOverride1"} TwoErrors replaces Foo { 
  // missing error
  method {:extern "BarNameOverride2", "ZazOverride2"} Zaz() returns (i: int) 
    ensures i >= 2

  // missing error
  method {:extern "ZapOverride2"} Zap() returns (i: int) 
    ensures i >= 2
}

replaceable module {:extern "FaaNameOverride"} Faa {
  method {:extern "ZazOverride1"} Zaz() returns (i: int) 
    ensures i >= 2
}

module {:extern} NoErrors replaces Faa { 
  method {:extern} Zaz() returns (i: int) 
    ensures i >= 2
}