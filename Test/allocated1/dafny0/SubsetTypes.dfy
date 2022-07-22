// RUN: %dafny_0 /verifyAllModules /allocated:1 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/SubsetTypes.dfy"
