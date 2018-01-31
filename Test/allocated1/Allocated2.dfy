// RUN: %dafny /verifyAllModules /allocated:2 /errorLimit:99 /errorTrace:0 /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "AllocatedCommon.dfyi"
