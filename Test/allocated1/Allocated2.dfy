
// RUN: %exits-with 2 %dafny /verifyAllModules /allocated:2 /errorLimit:99 /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "AllocatedCommon.dfyi"
