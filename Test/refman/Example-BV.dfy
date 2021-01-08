// RUN: %dafny /verifyAllModules /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../docs/DafnyRef/examples/Example-BV.dfy"
