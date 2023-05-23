// RUN: %exits-with 4 %dafny /verifyAllModules /deprecation:0 /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Basics.dfy"
