// RUN: %dafny /verifyAllModules /allocated:1 /env:0 /print:"%t.print" /rprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/AutoContracts.dfy"
