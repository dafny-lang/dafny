// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %dafny /verifyAllModules /allocated:1 /noVerify "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/DirtyLoops.dfy"
