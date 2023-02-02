// RUN: %exits-with 4 %dafny /verifyAllModules /proverOpt:O:smt.qi.eager_threshold=80 /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 /optimizeResolution:0 /errorLimit:20 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Fuel.dfy"
