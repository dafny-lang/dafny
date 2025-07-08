// RUN: ! %run %s > %t
// RUN: %diff "%s.expect" "%t"

replaceable module {:extern "FooNameOverride"} Foo {
  method {:axiom} {:extern "ZazOverride1"} Zaz() returns (i: int) 
    ensures i >= 2

  method {:axiom} {:extern "ZapOverride1"} Zap() returns (i: int) 
    ensures i >= 2
}

module {:extern "BarNameOverride1"} TwoErrors replaces Foo { 
  // missing error
  method {:axiom} {:extern "BarNameOverride2", "ZazOverride2"} Zaz() returns (i: int) 
    ensures i >= 2

  // missing error
  method {:axiom} {:extern "ZapOverride2"} Zap() returns (i: int) 
    ensures i >= 2
}

replaceable module {:extern "FaaNameOverride"} Faa {
  method {:axiom} {:extern "ZazOverride1"} Zaz() returns (i: int) 
    ensures i >= 2
}

module {:extern} NoErrors replaces Faa { 
  method {:axiom} {:extern} Zaz() returns (i: int) 
    ensures i >= 2
}