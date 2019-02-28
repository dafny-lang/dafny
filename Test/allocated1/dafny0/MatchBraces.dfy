// RUN: %dafny /verifyAllModules /allocated:1 /print:"%t.print" /compile:3 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/MatchBraces.dfy"
