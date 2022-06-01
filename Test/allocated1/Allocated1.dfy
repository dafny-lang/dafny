
// RUN: %dafny_0 /verifyAllModules /allocated:1 /errorLimit:99 /compile:0 /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "AllocatedCommon.dfyi"
