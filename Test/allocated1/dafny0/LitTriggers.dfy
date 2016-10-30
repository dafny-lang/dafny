// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /dprint:"%t.dprint" /autoTriggers:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/LitTriggers.dfy"
