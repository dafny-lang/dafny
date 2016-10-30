// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /env:0 /rprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/TypeConversions.dfy"
