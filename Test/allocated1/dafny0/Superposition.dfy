// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /compile:0 /tracePOs /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Superposition.dfy"
