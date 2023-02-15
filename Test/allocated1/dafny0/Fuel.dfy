// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 /optimizeResolution:0 /errorLimit:10 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Fuel.dfy"
