// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %dafny /verifyAllModules /allocated:1 /noVerify /compile:1 "%t.dprint.dfy" >> "%t"
include "../../dafny0/DirtyLoops.dfy"
