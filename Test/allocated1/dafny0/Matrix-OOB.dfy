// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /compile:0 /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Matrix-OOB.dfy"
