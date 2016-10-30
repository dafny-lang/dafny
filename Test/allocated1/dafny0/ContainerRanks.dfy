// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/ContainerRanks.dfy"
