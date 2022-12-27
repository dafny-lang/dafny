// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Unchanged.dfy"
