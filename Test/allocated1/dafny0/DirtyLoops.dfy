// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /compile:0 /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %exits-with 0 %dafny /verifyAllModules /allocated:1 /noVerify "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/DirtyLoops.dfy"
