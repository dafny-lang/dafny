// RUN: %dafny /compile:0 /verifyAllModules "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This tests that an example in the Reference Manual behaves as expected

include "../../docs/DafnyRef/examples/Example-Old2.dfy"
