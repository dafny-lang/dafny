// RUN: %dafny /verifyAllModules /allocated:1 /compile:3 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/SeqFromArray.dfy"
