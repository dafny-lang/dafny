// RUN: %dafny /verifyAllModules /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../docs/DafnyRef/examples/Example-Old3.dfy"
