// RUN: %dafny /verifyAllModules /allocated:1 /compile:3 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/ForallCompilation.dfy"
