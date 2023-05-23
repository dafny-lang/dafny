// RUN: %exits-with 4 %dafny /verifyAllModules /deprecation:0 /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/FunctionSpecifications.dfy"
