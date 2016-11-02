// RUN: %dafny /verifyAllModules /allocated:1 /errorLimit:99 /errorTrace:0 /compile:0 /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "AllocatedCommon.dfyi"
