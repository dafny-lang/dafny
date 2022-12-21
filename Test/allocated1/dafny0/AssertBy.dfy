// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/AssertBy.dfy"
